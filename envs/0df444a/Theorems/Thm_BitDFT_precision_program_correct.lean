-- Prove2me | Theorems.Thm_BitDFT_precision_program_correct
-- name    : BitDFT.precision_program_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:36:16.342783+00:00
-- url     : https://prove2.me/theorems/f79da9c6-12c0-43a0-bd30-5f4d2ec309d6
-- title:
--   The combined finite precision program computes q in at most 7q transitions
-- statement:
--   Let n be represented by a canonical binary word with a leading one, and let w encode a positive requested precision b with |w|≤b. Set q=b+3 max(ceil(log₂ n),1)+5. Starting with these two words in the specified work-tape layout and an empty unary workspace, the single fixed five-tape program halts in at most 7q transitions with a little-endian binary word of value q and length at most q. It retains the dimension word and arbitrary native input/output data, clears the unary workspace, and parks its heads in the specified final configuration. The program constructs its own logarithmic unary increment; no such increment is supplied as an input. Initial request parsing and final header serialization are outside this stage.
-- source:
--   Reuses the accepted scanner, binary counter with bounded output length, exact-clock tape extension/permutation, and machine-sequencing theorems. The proof verifies the exact physical handoff layout before adding the clocks. This is a complete precision-computation stage, not a complete rescaling wrapper or Fourier transfer proof.

import Definitions.Def_BitDFT_PrecisionProgram
import Definitions.Def_BitDFT_Numerics
open BitDFT BitDFT.PrecisionProgram IntMul

theorem BitDFT.precision_program_correct (base : arithmetic.Cfg) (tail w : List Bool)
    (hb : 1 ≤ IntMul.val w) (hw : w.length ≤ IntMul.val w) :
    let q := BitDFT.guardPrecision (IntMul.val (true::tail)) (IntMul.val w)
    ∃ t v, t ≤ 7*q ∧ BinaryCounter.value v = q ∧ v.length ≤ q ∧
      machine.step^[t] (initial base tail w) = final base tail v := by sorry
