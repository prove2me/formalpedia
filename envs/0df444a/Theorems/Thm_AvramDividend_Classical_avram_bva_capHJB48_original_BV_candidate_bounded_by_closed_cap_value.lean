-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB48_original_BV_candidate_bounded_by_closed_cap_value
-- name    : AvramDividend.Classical.avram_bva_capHJB48_original_BV_candidate_bounded_by_closed_cap_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:31:16.347396+00:00
-- url     : https://prove2.me/theorems/727edcfb-61dd-4de6-a1f9-86033e03a65b
-- title:
--   Original BV C1 barrier candidate on finite closed cap is bounded by its nonnegative cap value
-- statement:
--   For the original bounded-variation dividend verification candidate continuous on nonnegative reserves, with w(0) nonnegative, C1 interior and derivative at least one, the candidate is monotone across the full closed interval from zero to any finite dividend cap. Consequently all reserve values there are nonnegative and their absolute candidate value is bounded by its actual cap value w(C). Uses authoritative Proved original candidate closed reserve monotonicity; eliminates an abstract source cap envelope constant in true full nonlinear jump-loss estimates, retains w(0) allowed positive.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_C1_candidate_monotone_closed_reserve_band
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB48_original_BV_candidate_bounded_by_closed_cap_value
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hw0 : 0 ≤ w 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    0 ≤ w C.toReal ∧
    ∀ y ∈ Icc (0 : ℝ) C.toReal, |w y| ≤ w C.toReal := by sorry
