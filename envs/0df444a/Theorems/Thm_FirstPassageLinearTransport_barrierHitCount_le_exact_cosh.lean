-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_barrierHitCount_le_exact_cosh
-- name    : FirstPassageLinearTransport.barrierHitCount_le_exact_cosh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:11:44.540168+00:00
-- url     : https://prove2.me/theorems/e562b367-ed7a-5a17-b519-70d95224cb5e
-- title:
--   First Passage Linear Transport: barrier Hit Count le exact cosh
-- statement:
--   Exact finite cosh-potential estimate, with no quadratic relaxation.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/EntropyBarrier.lean#L36-L88
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/EntropyBarrier.lean#L36-L88

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.barrierHitCount_le_exact_cosh
    (a θ : ℝ) (M : ℕ) (ha : 0 ≤ a) (hθ : 0 ≤ θ) :
    (barrierHitCount a M 0 : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp ((M : ℝ) * Real.log (Real.cosh θ) - θ * a) := by sorry
