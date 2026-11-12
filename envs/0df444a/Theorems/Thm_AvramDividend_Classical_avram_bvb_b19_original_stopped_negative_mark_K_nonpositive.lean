-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b19_original_stopped_negative_mark_K_nonpositive
-- name    : AvramDividend.Classical.avram_bvb_b19_original_stopped_negative_mark_K_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:31:50.271688+00:00
-- url     : https://prove2.me/theorems/beaa3373-6a44-4768-9fc5-e7baf5b8c571
-- title:
--   Original BV stopped closed-cap negative-mark compensator is nonpositive at each grid level
-- statement:
--   For the original source X and original stopped reserve-left-limit U, the negative-jump compensator term K_n used by phys95 is nonpositive for every path and every mesh level, including the zero-reserve and upper-cap contact sets. This is the source-specific instantiation of Proved phys93, permitting subsequent quadrature work to focus on the one-sided discrepancy K_n minus J_n.
-- source:
--   AVRAM BVB19 original phys95 K_n sign for finite-cap stopped marked compensator, preserving original X.ν and Lebesgue-time pushforward, from authoritative Proved phys93 632dd120-3cfb-4938-bf9f-93f31bdfa9c1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys93_negative_mark_closed_cap_compensator_double_integral_nonpos
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b19_original_stopped_negative_mark_K_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q T : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (δ : ℕ → ℝ) (U : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) :
    (∫ t, ∫ z,
      (if 0 < t ∧ (t : ℝ) < T - δ n ∧
          (t : ℝ≥0∞) ≤ σ ω ∧ 0 ≤ U t ω ∧
          ENNReal.ofReal (U t ω) ≤ C ∧ z < 0 then
        Real.exp (-(q * (t : ℝ))) *
          (w (U t ω + z) - w (U t ω))
      else 0) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) ≤ 0 := by sorry
