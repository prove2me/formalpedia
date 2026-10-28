-- Prove2me | Theorems.Thm_BitDFT_suffix_copy_correct
-- name    : BitDFT.suffix_copy_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:37:15.302045+00:00
-- url     : https://prove2.me/theorems/d46233f1-f249-408c-8583-55fa2087a508
-- title:
--   Append a native input suffix in exactly |r|+1 transitions
-- statement:
--   Given native input pr, existing output o, and the input head at the first bit of r, the fixed copying machine appends exactly r to output in |r|+1 transitions. It halts at the input separator with its output head immediately after or. The entire input and all workspace cells and heads are preserved; the complete final configuration includes the exact blank tail of output. Empty r is allowed.
-- source:
--   Actual finite-machine suffix copying needed to assemble the full rewritten Fourier input after native header rewriting.

import Definitions.Def_BitDFT_SuffixCopy
open BitDFT.SuffixCopy IntMul

theorem BitDFT.suffix_copy_correct (base : machine.Cfg) (pre rest out : List Bool) :
    machine.step^[rest.length+1] (frame base .copy (pre++rest) out (pre.length+1)) =
      frame base .halt (pre++rest) (out++rest) (pre.length+rest.length+1) := by sorry
