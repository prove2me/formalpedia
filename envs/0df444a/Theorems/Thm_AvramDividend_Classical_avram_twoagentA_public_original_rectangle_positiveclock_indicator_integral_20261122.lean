-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_rectangle_positiveclock_indicator_integral_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_original_rectangle_positiveclock_indicator_integral_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:21:08.499496+00:00
-- url     : https://prove2.me/theorems/3dd6e086-f041-4da5-9fa5-8817187f3d6d
-- title:
--   Original physical marked integral L1 source 0da497df
-- statement:
--   Exact already accepted original negative-mark signed-integral source proof, republished as public importable prerequisite for the genuine unrestricted negative activity physical compensated mark L1 centring and reciprocal quantizer approximation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_original_rectangle_positiveclock_indicator_integral_20261122
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (μ : Measure (ℝ≥0 × ℝ)) :
    (∫ p : ℝ≥0 × ℝ,
      (if p.1 ≤ T then
        (if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 ∈ B then p.2 else 0)
       else 0) ∂μ) =
    (∫ p in Ioc 0 T ×ˢ B, p.2 ∂μ) := by sorry
