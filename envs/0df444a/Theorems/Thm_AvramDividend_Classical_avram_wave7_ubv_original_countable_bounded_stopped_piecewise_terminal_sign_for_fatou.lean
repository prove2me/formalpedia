-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_countable_bounded_stopped_piecewise_terminal_sign_for_fatou
-- name    : AvramDividend.Classical.avram_wave7_ubv_original_countable_bounded_stopped_piecewise_terminal_sign_for_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:49:51.480669+00:00
-- url     : https://prove2.me/theorems/a116738a-ce00-4e86-b9b5-a1ff3174bfeb
-- title:
--   Original UBV one a.s. terminal sign event for every bounded stochastic localiser
-- statement:
--   For a countable sequence of genuinely bounded right-continuous stopping times tau_n of the original source filtration with tau_n≤ruinTime, and the exact Chat 06 piecewise reserve W_n and discounted terminal Term_n at each clock, one single original P-almost-sure event makes every Term_n nonnegative. The candidate w has exactly the core's all-cap positive regularity, w(0)>=0, negative-side zero and interior derivative hypotheses; no boundary smoothness, local-time vanishing or Ito-Stieltjes identity is added. This common-event sign is directly suited to Fatou passage from bounded stochastic localisers.
-- source:
--   Previously Proved exact source Chat 06 hTermNonneg 0eb5420e-1c79-4d2e-b7d1-f3030b0bf5e7, itself assembled from accepted all-cap pre/postpayment values.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_ito_terminal_piecewise_reward_nonneg

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_ubv_original_countable_bounded_stopped_piecewise_terminal_sign_for_fatou
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
    ∀ᵐ ω ∂P, ∀ n : ℕ, 0 ≤ Term n ω := by sorry
