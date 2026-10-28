-- Prove2me | Theorems.Thm_BitDFT_parsed_precision_correct
-- name    : BitDFT.parsed_precision_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:06:05.584577+00:00
-- url     : https://prove2.me/theorems/3ce8ce13-dc24-44a0-95a7-47fde1e4322e
-- title:
--   Compute guard precision from retained parsed headers
-- statement:
--   Let a canonical binary word encode positive n, and let w encode positive b with |w|≤b. Write q=b+3 max(ceil(log₂ n),1)+5. From the specified layout of retained parsed headers, a single fixed machine halts with a little-endian word of value q and length at most q in at most 7q+2|w|+|tail|+6 steps, where tail is the dimension word after its leading one. The source workspace is cleared and native caller tapes are preserved. The machine performs its own reversal and head setup; parsing headers from native input and serializing the result are not included in this stage.
-- source:
--   Combines the exact-clock header setup theorem and the accepted precision-program theorem using a verified full-configuration handoff and the finite-controller sequencing theorem. This is a supporting component, not a proof of the complete Fourier transfer.

import Definitions.Def_BitDFT_ParsedPrecision
import Definitions.Def_BitDFT_Numerics
open BitDFT BitDFT.ParsedPrecision IntMul

theorem BitDFT.parsed_precision_correct (base : PrecisionProgram.arithmetic.Cfg) (tail w : List Bool)
    (hb : 1 ≤ IntMul.val w) (hw : w.length ≤ IntMul.val w) :
    let q := guardPrecision (IntMul.val (true::tail)) (IntMul.val w)
    ∃ t v, t ≤ 7*q+2*w.length+tail.length+6 ∧ BinaryCounter.value v = q ∧ v.length ≤ q ∧
      machine.step^[t] (initial base tail w) = final base tail v := by sorry
