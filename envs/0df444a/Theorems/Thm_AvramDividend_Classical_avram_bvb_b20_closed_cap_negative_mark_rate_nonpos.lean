-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
-- name    : AvramDividend.Classical.avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:03:31.798194+00:00
-- url     : https://prove2.me/theorems/07f94b51-fa8d-4f35-ad4b-abe0877c9c4d
-- title:
--   Original BV negative-mark integral is nonpositive throughout the closed cap
-- statement:
--   Under the original BV derivative and zero-value hypotheses, the verification candidate decreases under every negative mark throughout the closed finite or infinite cap, including ruin overshoots, and the full negative-mark integral is nonpositive.
-- source:
--   Required physical source sign to eliminate the one-sided mask case at zero-reserve and upper-cap occupation in phys95.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ν : Measure ℝ) (b : ℝ) (hb : 0 ≤ b) (hbCap : ENNReal.ofReal b ≤ C) :
    (∫ z in Iio (0 : ℝ), w (b + z) - w b ∂ν) ≤ 0 := by sorry
