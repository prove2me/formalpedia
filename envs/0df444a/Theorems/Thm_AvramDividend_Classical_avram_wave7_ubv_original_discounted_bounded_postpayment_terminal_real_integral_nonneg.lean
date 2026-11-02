-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_discounted_bounded_postpayment_terminal_real_integral_nonneg
-- name    : AvramDividend.Classical.avram_wave7_ubv_original_discounted_bounded_postpayment_terminal_real_integral_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:26:53.281265+00:00
-- url     : https://prove2.me/theorems/2d9e0944-ea6b-43b7-845d-fd1c0dcda2c9
-- title:
--   Original UBV discounted postpayment right-limit stopped terminal real integral is nonnegative
-- statement:
--   For the actual original SpectrallyNegativeLevy P 𝓕 and admissible D in unbounded variation, the discounted real integral of w(x+X_t-rightLimit D_t) at t=(τ∧T).toNNReal is nonnegative for every original 𝓕.rightCont stopping time τ and finite real nonnegative clip T. Reuse the Proved original all-cap postpayment pointwise nonnegativity and multiply by positive Real.exp. Handles creeping into zero via w(0)>=0, negative overshoot via w(y)=0 for y<0 and infinite τ via finite clipping. No terminal integrability or controlled dividend Stieltjes calculation is asserted.
-- source:
--   Proved all-cap original postpayment terminal nonnegative theorem 06839544-2429-48b2-bce8-78e4b76dd814 and original source filtration. Sign handoff only, distinct from Chat 04-B dividend integration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_ubv_original_discounted_bounded_postpayment_terminal_real_integral_nonneg
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
    0 ≤ (∫ ω, Real.exp (-q * ((min (τ ω) (T : ℝ≥0∞)).toNNReal : ℝ)) *
      w (x + X.X (min (τ ω) (T : ℝ≥0∞)).toNNReal ω -
        rightLimit D (min (τ ω) (T : ℝ≥0∞)).toNNReal ω) ∂P) := by sorry
