-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_discounted_bounded_postpayment_positive_part_lintegral_domination
-- name    : AvramDividend.Classical.avram_wave7_ubv_original_discounted_bounded_postpayment_positive_part_lintegral_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:32:29.214271+00:00
-- url     : https://prove2.me/theorems/78f544d8-ab7e-498b-b53c-9a2af6100d35
-- title:
--   Original UBV discounted postpayment stopped terminal positive-part expectation is dominated by w
-- statement:
--   For the actual original SpectrallyNegativeLevy P 𝓕 in the unbounded-variation regime and actual admissible dividend D, at any genuine original right-continuous stopping time τ finitely clipped by T, the extended discounted expectation of max(0,x+X_t-rightLimit D_t) is bounded by the corresponding extended expectation of w of the same postpayment reserve. It follows from the accepted all-cap postpayment positive-part pointwise bound, multiplication by the positive exponential and ENNReal lower-integral monotonicity. Handles creeping at zero and negative overshoot without new smoothness, martingale integrability or Stieltjes decomposition assumptions.
-- source:
--   Proved original all-cap postpayment positive-part domination 9ae5dedd-b82e-4205-9f96-af361b8e4e08; zero boundary corrected core 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_ubv_original_discounted_bounded_postpayment_positive_part_lintegral_domination
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
        max 0 (x + X.X (min (τ ω) (T : ℝ≥0∞)).toNNReal ω -
          rightLimit D (min (τ ω) (T : ℝ≥0∞)).toNNReal ω)) ∂P) ≤
    (∫⁻ ω, ENNReal.ofReal (
        Real.exp (-q * ((min (τ ω) (T : ℝ≥0∞)).toNNReal : ℝ)) *
        w (x + X.X (min (τ ω) (T : ℝ≥0∞)).toNNReal ω -
          rightLimit D (min (τ ω) (T : ℝ≥0∞)).toNNReal ω)) ∂P) := by sorry
