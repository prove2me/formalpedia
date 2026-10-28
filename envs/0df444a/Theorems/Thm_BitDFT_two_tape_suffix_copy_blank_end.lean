-- Prove2me | Theorems.Thm_BitDFT_two_tape_suffix_copy_blank_end
-- name    : BitDFT.two_tape_suffix_copy_blank_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T08:54:39.522547+00:00
-- url     : https://prove2.me/theorems/9faf99c5-2e36-4680-892a-b3b3b5c65ed0
-- title:
--   Copy a bit suffix directly to its blank terminator
-- statement:
--   For a source tape containing a prefix followed by a finite bit suffix and then blank, the two-tape copier appends exactly that suffix to the destination in one transition per bit and one final transition to detect blank. The halted frame preserves the source and has the destination head immediately after the copied suffix.
-- source:
--   This exact run theorem lets the scaler copy the low q magnitude bits from the blank-ended extracted coordinate without first writing a separator.

import Definitions.Def_BitDFT_BlankEndCopyFrame
import Mathlib.Data.List.GetD
import Mathlib.Tactic
open IntMul BitDFT BitDFT.SuffixCopyTwoTape

theorem BitDFT.two_tape_suffix_copy_blank_end (base : machine.Cfg) (pre rest out : List Bool) :
    machine.step^[rest.length+1]
      (blankEndFrame base .copy (pre++rest) out (pre.length+1)) =
    blankEndFrame base .halt (pre++rest) (out++rest)
      (pre.length+rest.length+1) := by sorry
