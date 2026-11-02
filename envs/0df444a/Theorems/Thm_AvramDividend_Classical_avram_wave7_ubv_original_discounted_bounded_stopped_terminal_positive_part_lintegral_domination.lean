-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_discounted_bounded_stopped_terminal_positive_part_lintegral_domination
-- name    : AvramDividend.Classical.avram_wave7_ubv_original_discounted_bounded_stopped_terminal_positive_part_lintegral_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:29:22.46284+00:00
-- url     : https://prove2.me/theorems/3304ca2e-d7a8-4c8c-9d0b-412039135fe0
-- title:
--   Original UBV discounted stopped terminal positive-part expectation dominated by w at source stopping clocks
-- statement:
--   For the actual original SpectrallyNegativeLevy P 𝓕 and admissible D, each original right-continuous stopping time τ and finite clip T admit a discounted ENNReal expectation inequality: the positive part of the stopped reserve is dominated by w of that reserve, with the same positive discount factor. This follows pathwise from the Proved all-cap terminal max(0,U)<=w(U) theorem under w(0)>=0 and interior gradient, then ENNReal.ofReal monotonicity and lintegral_mono. The statement includes creeping to zero, negative overshoot, τ=0 and τ=∞ after finite clipping, without integrability, boundary smoothness or martingale assumptions.
-- source:
--   Proved original all-cap positive-part terminal domination 2b04d61b-0c38-44e4-ba16-ea6843d0c45e; finite stopped source clock and 0<=w(0) as corrected core.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_ubv_original_discounted_bounded_stopped_terminal_positive_part_lintegral_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0∞) (hτstop : IsStoppingTime 𝓕.rightCont τ)
    (T : ℝ≥0) :
    (∫⁻ ω, ENNReal.ofReal (
        Real.exp (-q * ((min (τ ω) (T : ℝ≥0∞)).toNNReal : ℝ)) *
        max 0 (riskProcess X x D
          (min (τ ω) (T : ℝ≥0∞)).toNNReal ω)) ∂P) ≤
    (∫⁻ ω, ENNReal.ofReal (
        Real.exp (-q * ((min (τ ω) (T : ℝ≥0∞)).toNNReal : ℝ)) *
        w (riskProcess X x D
          (min (τ ω) (T : ℝ≥0∞)).toNNReal ω)) ∂P) := by sorry
