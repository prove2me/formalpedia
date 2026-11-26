-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_barrierHitCount_le_binaryEntropy
-- name    : FirstPassageLinearTransport.barrierHitCount_le_binaryEntropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:12:42.681802+00:00
-- url     : https://prove2.me/theorems/f28bf744-5cae-5a30-b5d2-390b96a0b722
-- title:
--   First Passage Linear Transport: barrier Hit Count le binary Entropy
-- statement:
--   Entropy-sharp two-sided maximal Boolean-walk estimate.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/EntropyBarrier.lean#L183-L190
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/EntropyBarrier.lean#L183-L190

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.barrierHitCount_le_binaryEntropy
    (t : ℝ) (M : ℕ) (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    (barrierHitCount (2 * t * M) M 0 : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-((M : ℝ) * binaryBarrierRate t)) := by sorry
