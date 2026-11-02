-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_countable_bounded_stopped_piecewise_terminal_real_integrals_nonneg
-- name    : AvramDividend.Classical.avram_wave7_ubv_original_countable_bounded_stopped_piecewise_terminal_real_integrals_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:52:42.177208+00:00
-- url     : https://prove2.me/theorems/8eb0098c-1dc8-408c-998c-38cc132b5629
-- title:
--   Original UBV nonnegative real expected exact Chat 06 terminal terms at every bounded localiser
-- statement:
--   For the actual original source X, admissible D, and countably many bounded genuine right-continuous stopping clocks tau_n≤ruin, each with Chat 06's precise piecewise W_n and discounted Term_n, show every real Bochner integral ∫Term_n dP is nonnegative. Apply the previously accepted exact terminal sign a.e theorem independently at each n and Mathlib integral_nonneg_of_ae. This proves signs only, not integrability, full Ito decomposition or Stieltjes dividend budgets; zero creeping uses only w(0)>=0.
-- source:
--   Proved exact original Chat 06 terminal sign 0eb5420e-1c79-4d2e-b7d1-f3030b0bf5e7; pinned Mathlib integral_nonneg_of_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_ito_terminal_piecewise_reward_nonneg

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_ubv_original_countable_bounded_stopped_piecewise_terminal_real_integrals_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : ℕ → Ω → ℝ≥0) (T : ℕ → ℝ≥0)
    (hτBound : ∀ n ω, τ n ω ≤ T n)
    (hτstop : ∀ n, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ n ω : WithTop ℝ≥0)))
    (hτruin : ∀ n ω, (τ n ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (W Term : ℕ → Ω → ℝ)
    (hW : ∀ n ω, W n ω =
      if (τ n ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ n ω) ω - rightLimit D (τ n ω) ω
      else riskProcess X x D (τ n ω) ω)
    (hTerm : ∀ n ω, Term n ω =
      Real.exp (-(q * (τ n ω : ℝ))) * w (W n ω)) :
    ∀ n : ℕ, 0 ≤ ∫ ω, Term n ω ∂P := by sorry
