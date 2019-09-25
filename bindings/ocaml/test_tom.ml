(** Tom's test x86 disassembly program **)

open Printf
open Capstone
open X86
open X86_const

let print_string_hex comment str =
	printf "%s" comment;
	Array.iter (printf "0x%02x ") str;
	printf "\n"

let _X86_CODE64 = "\x55\x48\x8b\x05\xb8\x13\x00\x00"

let all_tests = [
		(CS_ARCH_X86, [CS_MODE_64], _X86_CODE64, "X86 64 (Intel syntax)", 0L);
	]

let print_op handle i op =
	match op.value with
	| X86_OP_INVALID _ -> ()	(* this would never happens *)
	| X86_OP_REG reg -> (
		printf "\t\top[%d]: REG = [0x%x]" i reg;
		flush stdout;
		printf " %s\n" (cs_reg_name handle reg)
	)
	| X86_OP_IMM imm -> printf "\t\top[%d]: IMM = 0x%x\n" i imm.value
	| X86_OP_MEM mem -> ( printf "\t\top[%d]: MEM\n" i;
		if mem.base != 0 then
			printf "\t\t\toperands[%u].mem.base: REG = %s\n" i (cs_reg_name handle  mem.base);
		if mem.index != 0 then
			printf "\t\t\toperands[%u].mem.index: REG = %s\n" i (cs_reg_name handle mem.index);
		if mem.scale != 1 then
			printf "\t\t\toperands[%u].mem.scale: %d\n" i mem.scale;
		if mem.disp != 0 then
			printf "\t\t\toperands[%u].mem.disp: 0x%x\n" i mem.disp;
		)

let print_detail handle mode insn =
	match insn.arch with
	| CS_INFO_X86 x86 -> (
			print_string_hex "\tPrefix: " x86.prefix;

			(* print instruction's opcode *)
			print_string_hex "\tOpcode: " x86.opcode;

			(* print operand's size, address size, displacement size & immediate size *)
			printf "\taddr_size: %u\n" x86.addr_size;

			(* print modRM byte *)
			printf "\tmodrm: 0x%x\n" x86.modrm;

			(* print displacement value *)
			if x86.disp != 0 then
			printf "\tdisp: 0x%x\n" x86.disp;

			(* SIB is invalid in 16-bit mode *)
			if not (List.mem CS_MODE_16 mode) then (
				(* print SIB byte *)
				printf "\tsib: 0x%x\n" x86.sib;

				(* print sib index/scale/base (if applicable) *)
				if x86.sib_index <> _X86_REG_INVALID then
					printf "\tsib_index: 0x%x, sib_scale: %u, sib_base: 0x%x\n"
						x86.sib_index x86.sib_scale x86.sib_base ;
				(*printf "\tsib_index: %s, sib_scale: %u, sib_base: %s\n"
				(cs_reg_name handle x86.sib_index)
				x86.sib_scale
				(cs_reg_name handle x86.sib_base);
				*)
			);

			(* print all operands info (type & value) *)
			if (Array.length x86.operands) > 0 then (
				printf "\top_count: %d\n" (Array.length x86.operands);
				Array.iteri (print_op handle) x86.operands;
			);
			printf "\n";
	)
	| _ -> ()

let print_insn handle mode insn =
	printf "0x%x\t" insn.address;
	Array.iter (printf "%02x ") insn.bytes;
	printf "\t%s\t%s\n" insn.mnemonic insn.op_str;
	print_detail handle mode insn

let print_arch x =
	let (arch, mode, code, comment, syntax) = x in
	let handle = cs_open arch mode in
	if syntax != 0L then (
		let err = cs_option handle CS_OPT_SYNTAX syntax in
		match err with
		| _ -> ();
	);
	let err = cs_option handle CS_OPT_DETAIL _CS_OPT_ON in
	match err with
	| _ -> ();
	let insns = cs_disasm handle code 0x1000L 0L in (
		printf "*************\n";
		printf "Platform: %s\n" comment;
		List.iter (print_insn handle mode) insns;
	);
	match cs_close handle with
	| 0 -> ()
	| _ -> printf "Failed to close handle"


let align_n n x = Int64.logand (Int64.shift_left 0xFFFFFFFFFFFFFFFFL n) x
let align8 x = align_n 3 x
let align16 x = align_n 4 x
let align32 x = align_n 5 x
let align64 x = align_n 6 x

let int32_unsigned_compare (n:Int32.t) (m:Int32.t) =
  Int32.(compare (sub n min_int) (sub m min_int))

let insn_in_groups insn grps =
	let insn_in_group g = Array.mem g insn.groups in
	List.exists insn_in_group grps

let insn_dissasmble_str insn =
	String.concat "\t" [insn.mnemonic; insn.op_str]

let rec array_find_some fn a =
	let n = Array.length a in
	let rec loop i =
		if i = n then None
		else match fn (Array.unsafe_get a i) with
			| Some x -> Some x
			| None -> loop (succ i)
	in
	loop 0

(*
	Assembly/Compiler Coding Rule 10. (M impact, L generality)
	Do not put more than four branches in a 16-byte chunk.
*)
module R10 = struct
	type chunk = {
				 	addr0: Int64.t; (* start address of 16-byte chunks*)
 					mutable n_branches: int; (* number of branches *)
				 }
	type t = 	 {
					cur_chunk: chunk;
					flagged_chunks: chunk list;
				 }

	let empty_state () =
		{
			cur_chunk={addr0=0L; n_branches=0};
			flagged_chunks=[];
		}

	let step_state (state:t) insn =
	 	let insn_addr = Int64.of_int insn.address in
	    let insn_chunk_addr0 = align16 insn_addr in
	    let state =
	    	if insn_chunk_addr0 <> state.cur_chunk.addr0
	    	then begin
	    		let flagged_chunks =
	    			if state.cur_chunk.n_branches >= 4
	    			then state.cur_chunk :: state.flagged_chunks
	    			else state.flagged_chunks in
	    		{
	    			cur_chunk={addr0=insn_chunk_addr0; n_branches=0};
	    			flagged_chunks=flagged_chunks
	    		}
	    	end
	    	else state in
		if insn_in_groups insn [_CS_GRP_JUMP; _CS_GRP_CALL; _CS_GRP_RET]
	    then state.cur_chunk.n_branches <- state.cur_chunk.n_branches + 1;
	    state

	let print (state:t) =
		let print_chunk c =
			printf "[R10]  0x%Lx\tn_branches: %d\n" c.addr0 c.n_branches in
		List.iter print_chunk (List.rev state.flagged_chunks)
end

(*
	Assembly/Compiler Coding Rule 21. (MH impact, MH generality)
	Favor generating code using imm8 or imm32 values instead of imm16 values.

	NB: can not replace a imm32 with an imm8 load in general as top bits of the
	register are left unchanged.

    We check displacements use (signed) 8-bit if they fit
        48 8b 5c 24 10          movq    0x10(%rsp), %rbx
	NOT
		48 8b 9b 10 00 00 00    movq    0x10(%rbx), %rbx
*)
module R21 = struct
	(* list of (flagged address, disassembly, imm, size) *)
	type t = (Int64.t * string * int * int) list

	let empty_state () = []

	let value_fits_in_signed8 n =
		let n = Int32.of_int n in
		-128l < n && n < 128l

	let check_imm_operand op =
		match op.value with
		| X86_OP_MEM mem when mem.disp_encoding_size == 4 && value_fits_in_signed8 mem.disp -> Some (mem.disp, mem.disp_encoding_size)
		| _ -> None

	let step_state (state:t) (insn:Capstone.cs_insn0) =
		(* we look for operands that are imm32 which fit in imm8 *)
		let flag =
			match insn.arch with
				| CS_INFO_X86 x86 when insn.mnemonic <> "nop" ->
					array_find_some check_imm_operand x86.operands
 				| _ -> None
		in
		match flag with
			| Some (imm, size) -> (Int64.of_int insn.address, insn_dissasmble_str insn, imm, size) :: state
			| None -> state

	let print (state:t) =
		let print_flagged_addr fa =
			let addr, str, imm, size = fa in
			printf "[R21]  0x%Lx\t%s\timm: %d\tsize: %u\n" addr str imm size
		in
		List.iter print_flagged_addr (List.rev state)
end

(*
	Assembly/Compiler Coding Rule 26. (ML impact, L generality)
	Use simple instructions that are less than eight bytes in length.
*)
module R26 = struct
	(* list of (flagged address, size, disassembly) *)
	type t = (Int64.t * int * string) list

	let empty_state () = []

	let step_state (state:t) (insn:Capstone.cs_insn0) =
		(* we look for instructions not less than 8 which aren't nops *)
		let state =
			if insn.size < 8 || insn.mnemonic = "nop"
			then state
			else (Int64.of_int insn.address, insn.size, insn_dissasmble_str insn) :: state
		in
		state

	let print (state:t) =
		let print_flagged_addr fa =
			let addr, size, str = fa in
			printf "[R26]  0x%Lx\tsize: %d\t%s\n" addr size str
		in
		List.iter print_flagged_addr (List.rev state)
end


(*
	Assembly/Compiler Coding Rule 64. (H impact, M generality)
	Use the 32-bit versions of instructions in 64-bit mode to reduce code size
	unless the 64-bit version is necessary to access 64-bit data or additional
	registers.
*)
module R64 = struct
	(* list of (flagged address, disassembly, imm, size) *)
	type t = (Int64.t * string * int * int) list

	let empty_state () = []

	let imm32_sign_extends_to_64 n =
		(Int32.of_int n) > 0l || true

	let check_mov_imm_reg64_could_be_reg32 insn x86 =
		(* check is a "mov" with 2 operands
	 	   AND first operand REG size 8
	 	   AND second operand IMM size 4
	 	   AND the IMM operand will sign extend to 64 correctly *)
		match insn.mnemonic with
			| "mov" when Array.length x86.operands = 2 -> begin
					let op1 = x86.operands.(0) in
					let op2 = x86.operands.(1) in
					match (op1.value, op2.value) with
						| (X86_OP_REG _, X86_OP_IMM imm) when op1.size = 8 && imm.encoding_size = 4 && imm32_sign_extends_to_64 imm.value ->
						    	Some (imm.value, imm.encoding_size)
						| _ -> None
				end
			| _ -> None


	let step_state (state:t) (insn:Capstone.cs_insn0) =
		(* we look for instructions that are moves to a 64bit register with an imm32 operand that could be sign extended correctly in a 32bit register *)

		let flag =
			match insn.arch with
				| CS_INFO_X86 x86 ->
					check_mov_imm_reg64_could_be_reg32 insn x86
 				| _ -> None
		in
		match flag with
			| Some (imm, size) -> (Int64.of_int insn.address, insn_dissasmble_str insn, imm, size) :: state
			| None -> state

	let print (state:t) =
		let print_flagged_addr fa =
			let addr, str, imm, size = fa in
			printf "[R64]  0x%Lx\t%s\timm: %d\tsize: %u\n" addr str imm size
		in
		List.iter print_flagged_addr (List.rev state)
end

type function_block = {
	start_addr: int;
	end_addr: int;
	name: string;
}

let parse_addr =
	(* on OSX there is a offset in the addresses so we mask off to 32bits *)
	let is_darwin =
		match Bos.OS.Cmd.(run_out Bos.Cmd.(v "uname" % "-s") |> to_string) with
			| Result.Ok x when x = "Darwin" -> true
			| Result.Ok x -> false
			| Result.Error (`Msg e) -> printf "WARN: failure running uname: %s\n" e; false
	in
	if is_darwin
	then fun s ->
		Int64.(to_int (logand 0xFFFFFFFFL (of_string s)))
	else fun s ->
		Int64.(to_int (of_string s))


let shell_exec cmd =
	let sh_cmd = Bos.Cmd.(v "sh" % "-c" % cmd) in
	Bos.OS.Cmd.(run_out sh_cmd |> to_lines)

let get_function_blocks filename =
	let blocks_from_lines lines =
		let record_from_list xs = {
			start_addr = parse_addr (List.nth xs 0);
			end_addr = parse_addr (List.nth xs 1);
			name = List.nth xs 2;
			} in
		List.map (fun l -> record_from_list (String.split_on_char ' ' l)) lines
	in

	let nm_cmd = String.concat " " ["nm -n"; filename; "| awk 'BEGIN {last_nme=\"\";last_addr=\"\"} ($2==\"t\" || $2==\"T\") {if(last_nme != \"\") printf(\"0x%s 0x%s %s\\n\",last_addr,$1,last_nme) ;  last_nme=$3; last_addr=$1}'"] in
	match shell_exec nm_cmd with
		| Ok xs -> blocks_from_lines xs
		| Error (`Msg e) -> printf "ERROR: Failure when running nm exec command:\n %s\n" e; []

let process_block buff block passes =
	let offset = block.start_addr in
	let n_bytes = block.end_addr - block.start_addr in
	let code = Bytes.sub_string buff offset n_bytes in
	let insns_to_read = 0L in (* when 0 read all instructions *)

	printf "String.length code: %d\n" (String.length code);

	let (arch, mode) = (CS_ARCH_X86, [CS_MODE_64]) in
	let handle = cs_open arch mode in
	match (cs_option handle CS_OPT_DETAIL _CS_OPT_ON) with
		| _ -> ();

	let insns = cs_disasm handle code (Int64.of_int offset) insns_to_read in

	List.iter (fun fn -> fn handle mode insns) passes;

	printf "Total instructions %d in %d bytes\n" (List.length insns) (String.length code);

	match cs_close handle with
		| 0 -> ()
		| _ -> printf " Failed to close handle"


let build_passes passes =
	printf "Will run the following passes: %s\n" passes;
	let passes = String.split_on_char ',' passes in

	(* pass analysis functions over the data *)
	let fn cfg handle mode insns =
		let (empty_fn, step_fn, print_fn) = cfg in
		let output = List.fold_left step_fn (empty_fn ()) insns in
		print_fn output
	in

	let add_stage fns pass =
		match pass with
		  | "dump" -> (fun handle mode insns -> List.iter (print_insn handle mode) insns)::fns
		  | "R10" -> (fn (R10.empty_state, R10.step_state, R10.print))::fns
  		  | "R21" -> (fn (R21.empty_state, R21.step_state, R21.print))::fns
  		  | "R26" -> (fn (R26.empty_state, R26.step_state, R26.print))::fns
  		  | "R64" -> (fn (R64.empty_state, R64.step_state, R64.print))::fns
  		  | _ -> printf "Can't dispatch unknown pass '%s'\n" pass; fns
  	in

	List.fold_left add_stage [] passes


let run filename passes =
	let in_file = open_in_bin filename in
	let file_bytes = in_channel_length in_file in
	printf "Will read from %s (%d bytes)\n" filename file_bytes;
	let buff = Bytes.create file_bytes in
	really_input in_file buff 0 file_bytes;

	let passes = build_passes passes in

	let blocks = get_function_blocks filename in
	let aux b =
		printf "\n0x%x 0x%x %s:\n" b.start_addr b.end_addr b.name;
		process_block buff b passes;
	in
	List.iter aux blocks;


open Cmdliner

let filename =
  let doc = "binary input filename" in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"FILE" ~doc)

let passes =
  let doc = "Which passes to run on the binary; comma seperated list (e.g. \"dump,R21,R64\"" in
  Arg.(value & opt string "R10,R21,R26,R64" & info ["passes"] ~docv:"PASSES" ~doc)

let prog =
  let info =
    let doc = "test for Intel optimization rule violations" in
    let man = [] in
    Term.info "test_tom" ~version:"v0.1" ~doc ~man
  in
  (Term.(const run $ filename $ passes), info)

let () = Term.exit (Term.eval prog)

