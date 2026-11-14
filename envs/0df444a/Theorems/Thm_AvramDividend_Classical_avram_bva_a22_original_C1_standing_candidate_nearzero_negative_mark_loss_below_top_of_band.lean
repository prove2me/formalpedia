-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_C1_standing_candidate_nearzero_negative_mark_loss_below_top_of_band
-- name    : AvramDividend.Classical.avram_bva_a22_original_C1_standing_candidate_nearzero_negative_mark_loss_below_top_of_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:11:57.396204+00:00
-- url     : https://prove2.me/theorems/b1d40d93-7d04-442d-9c26-335e96ce86f0
-- title:
--   Genuine original C1 verification candidate has nonnegative negative-mark loss at most its small spatial band top value
-- statement:
--   Under the exact original spectrally negative Lévy dividend verification assumptions on a candidate w: continuity on nonnegative reserves, nonnegative w at zero, zero values on negative reserves, continuously differentiable on strict interior reserves and derivative at least one, fix any positive spatial width epsilon strictly below the original dividend cap. For every genuine positive pre-mark reserve y no greater than epsilon and any original strictly negative Lévy mark z, prove the full candidate loss w(y)-w(y+z) is nonnegative and at most w(epsilon), including downward jumps crossing below zero when w(0) may be strictly positive. This uses the already Proved original C1 candidate closed-band monotonicity and original zero-band negative-mark loss theorem, eliminating an otherwise unproved additional monotonicity assumption in source BVA96 boundary-layer estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_C1_candidate_monotone_closed_reserve_band
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_C1_negative_jump_candidate_loss_uniform_zero_band_bound_without_zero_boundary_value
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_C1_standing_candidate_nearzero_negative_mark_loss_below_top_of_band
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C) :
    ∀ y ∈ Ioc (0 : ℝ) ε, ∀ z : ℝ, z < 0 →
      0 ≤ w y - w (y + z) ∧ w y - w (y + z) ≤ w ε := by sorry
