-- Prove2me | Theorems.Thm_BitDFT_header_reader_correct
-- name    : BitDFT.header_reader_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T13:54:39.2428+00:00
-- url     : https://prove2.me/theorems/c527fd43-000a-4663-afc8-f8a5c254188c
-- title:
--   A length-prefixed field is read and its remainder copied in exactly input length plus three steps
-- statement:
--   Let $v$ and $r$ be arbitrary binary words, and write $k=|v|$. On the native input $1^k0vr$, the fixed four-tape header reader halts after exactly
--   $$2k+|r|+4$$
--   actual transitions. Its complete native output is $r$, its field tape contains precisely $v$, and its unary-counter tape is blank beyond the permanent start marker. The counter head is at the start marker and the field head is immediately after $v$. Thus the cost equals the input length plus three. Empty fields, empty remainders and leading zero bits are included. This is a concrete parsing component for the finite-precision Fourier input format.
-- source:
--   Original direct execution proof for Definitions.Def_BitDFT_HeaderReader. Uses actual IntMul.MultitapeTM transitions. Tape-update invariants adapt the existing proved copy construction, https://prove2.me/submissions/69d83c43-de72-4472-86ad-45f6ea010014. This is a component of BitDFT.rescale_output_machine, not a claim that the full rescaling wrapper is proved.

import Definitions.Def_BitDFT_HeaderReader
open BitDFT.HeaderReader

theorem BitDFT.header_reader_correct (v rest : List Bool) :
    let x := List.replicate v.length true ++ false :: (v ++ rest)
    let t := 2 * v.length + rest.length + 4
    machine.HaltsWithOutput x [] t rest ∧
      (machine.step^[t] (machine.initCfg x [])).cells 3 = machine.tapeOf (v.map machine.bitSym) ∧
      (machine.step^[t] (machine.initCfg x [])).cells 2 = machine.tapeOf [] ∧
      (machine.step^[t] (machine.initCfg x [])).head 2 = 0 ∧
      (machine.step^[t] (machine.initCfg x [])).head 3 = v.length+1 := by sorry
