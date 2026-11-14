-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_C1_candidate_monotone_closed_reserve_band
-- name    : AvramDividend.Classical.avram_bva_a22_original_C1_candidate_monotone_closed_reserve_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:15:36.210449+00:00
-- url     : https://prove2.me/theorems/1a8260b0-ed44-4ff6-ad07-0c72baaadd5f
-- title:
--   Original bounded-variation HJB C1 candidate is monotone on every closed nonnegative reserve band under the cap
-- statement:
--   For the original C1 HJB verification candidate w continuous at the ruin boundary, differentiable in the positive cap interior with derivative at least one, the source-established globally monotone cap-linear extension agrees exactly with w on every closed reserve band [0,B] lying below the finite cap, or any closed finite band if the cap is infinite. Hence w is monotone on the whole band including zero and a finite-cap endpoint. This supplies the monotonicity hypothesis of the source-exact BV full-horizon terminal modulus theorem while preserving original candidate and cap conventions.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_allcap_linear_monotone_nonnegative
open Classical Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_C1_candidate_monotone_closed_reserve_band
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (B : ℝ) (hBC : C = ⊤ ∨ B ≤ C.toReal) :
    MonotoneOn w (Icc (0 : ℝ) B) := by sorry
