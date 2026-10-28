-- Prove2me | Theorems.Thm_BitDFT_header_setup_correct
-- name    : BitDFT.header_setup_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:01:53.513193+00:00
-- url     : https://prove2.me/theorems/7c304ef9-654b-46aa-a84f-00d45a0e70ea
-- title:
--   Parsed precision bits are installed in linear time
-- statement:
--   Given arbitrary binary words s and d on work tapes 3 and 4, with heads just past their ends and tape 2 empty, the fixed setup machine halts after exactly 2|s|+|d|+4 transitions. Tape 2 contains the reversal of s, tape 3 is empty, tape 4 still contains d, and all three work heads are at position 1. The native input/output cells and heads are preserved. This full-configuration statement holds for empty as well as nonempty words.
-- source:
--   Supporting actual-machine input preparation for the integer-multiplication-to-DFT transfer. It does not assume a reversal oracle or a free repositioning of tape heads; full request parsing and machine composition are separate obligations.

import Definitions.Def_BitDFT_HeaderSetup
open BitDFT.HeaderSetup IntMul

theorem BitDFT.header_setup_correct (base : machine.Cfg) (src dim : List Bool) :
    machine.step^[2*src.length+dim.length+4]
      (frame base .start src [] dim 0 (src.length+1) (dim.length+1)) =
      frame base .halt [] src.reverse dim 1 1 1 := by sorry
