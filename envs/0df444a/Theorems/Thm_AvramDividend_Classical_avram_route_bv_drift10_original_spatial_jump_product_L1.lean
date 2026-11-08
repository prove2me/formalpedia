-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift10_original_spatial_jump_product_L1
-- name    : AvramDividend.Classical.avram_route_bv_drift10_original_spatial_jump_product_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:41:20.330221+00:00
-- url     : https://prove2.me/theorems/62394d36-a8f7-499c-84ed-a2920dad2230
-- title:
--   Original BV spatial jump-loss kernel is L1 on the reserve-mark product measure
-- statement:
--   This is the exact source-specific integrability prerequisite for real Fubini: integrate the nonnegative original reserve loss w(y)-w(y+z) against the product of physical reserve volume on (0,epsilon] and the actual negative Lévy jump measure. Its finite product integral follows from the proved individual-mark spatial loss estimate, the original bounded-variation truncated first-moment integrability, and Tonelli for the nonnegative jointly measurable kernel. No finite-activity assumption is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_negative_mark_loss_nonneg
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_each_mark_spatial_loss_le
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_bv_drift10_original_spatial_jump_product_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hwzero : w 0 = 0)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C) (hε1 : ε ≤ 1) :
    Integrable (fun yz : ℝ × ℝ => w yz.1 - w (yz.1 + yz.2))
      ((volume.restrict (Ioc (0 : ℝ) ε)).prod (X.ν.restrict (Iio (0 : ℝ)))) := by sorry
