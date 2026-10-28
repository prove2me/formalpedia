-- Prove2me | Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
-- name    : BitDFT.two_tape_suffix_copy_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:57:37.042887+00:00
-- url     : https://prove2.me/theorems/7772550c-79a6-4b70-875b-4d1e73272862
-- title:
--   Copy a delimited suffix in exactly |r|+1 transitions
-- statement:
--   For an input consisting of a prefix followed by a bit suffix and a separator, with the input head at the first suffix bit, the two-tape copier appends exactly that suffix to the existing output in one transition per bit and one final transition to detect the separator. It halts with the input tape and exact output configuration as specified, including when the suffix is empty.
-- source:
--   Exact finite-time correctness of the two-tape copier used in the record-to-multiplier adapter.

import Definitions.Def_BitDFT_SuffixCopyTwoTape
open BitDFT.SuffixCopyTwoTape IntMul

theorem BitDFT.two_tape_suffix_copy_correct (base : machine.Cfg) (pre rest out : List Bool) :
    machine.step^[rest.length+1] (frame base .copy (pre++rest) out (pre.length+1)) =
      frame base .halt (pre++rest) (out++rest) (pre.length+rest.length+1) := by sorry
