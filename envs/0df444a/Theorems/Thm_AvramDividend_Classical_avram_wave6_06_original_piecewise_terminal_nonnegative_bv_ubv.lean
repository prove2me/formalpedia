-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_piecewise_terminal_nonnegative_bv_ubv
-- name    : AvramDividend.Classical.avram_wave6_06_original_piecewise_terminal_nonnegative_bv_ubv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:27:30.662205+00:00
-- url     : https://prove2.me/theorems/9cf7c436-ea1a-4d1d-8072-aa2c1bada0b2
-- title:
--   Actual piecewise postpayment-before-ruin terminal is nonnegative for C1 BV and C2 UBV HJB candidate
-- statement:
--   For original X, admissible D, any random τ and source piecewise W, prove the expected-budget terminal term exp(-qτ)w(W) is nonnegative pathwise and hence almost surely, under source w(0)>=0, continuity, zero negative reserve extension, positive cap, separate BV C1/UBV C2 smoothness and gradient w'≥1, with x in [0,C]. If τ is strictly before ruin, use the already Proved exact BV post-right-payment terminal sign or UBV post-right-payment sign, splitting X.BoundedVariation. At ruin, use the already Proved universal book riskProcess terminal sign. No global w≥0 hypothesis, no second derivative in BV and no stochastic identity are needed.
-- source:
--   Avram Palmowski Pistorius Prop 4(i) terminal sign on exact Chat06 W; composes Proved 28b04520 BV C1, 06839544 UBV C2, 52dd2155 book ruin and real exponential positivity, preserving w(0)≥0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_book_reserve_terminal_nonnegative_separate_gradient

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_06_original_piecewise_terminal_nonnegative_bv_ubv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ᵐ ω ∂P, 0 ≤ Term ω := by sorry
