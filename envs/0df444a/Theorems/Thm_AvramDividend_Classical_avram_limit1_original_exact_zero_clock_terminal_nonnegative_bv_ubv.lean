-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_original_exact_zero_clock_terminal_nonnegative_bv_ubv
-- name    : AvramDividend.Classical.avram_limit1_original_exact_zero_clock_terminal_nonnegative_bv_ubv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:41:48.509236+00:00
-- url     : https://prove2.me/theorems/c4a010f8-0e14-4979-93b4-6294023ad6e5
-- title:
--   Original closed-clock discounted terminal nonnegative at time zero, survival and ruin for both BV and UBV
-- statement:
--   Under exact capped original admissibility, root-style BV C1 or UBV C2 smoothness and interior derivative floor, the literal original piecewise post-right-payment W at any random NNReal clock, with the zero clock treated as postpayment even when ruinTime=0, has nonnegative discounted terminal reward at every path. Split on the zero-or-survival W branch, use original BV C1 or UBV C2 postpayment sign according to bounded variation, and use the accepted source book-risk terminal sign in the ruin branch; Real.exp is nonnegative. No terminal vanishing, stochastic residual, equality-in-law, or stronger boundary assumptions.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_book_reserve_terminal_nonnegative_separate_gradient

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_original_exact_zero_clock_terminal_nonnegative_bv_ubv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ ω, 0 ≤ Term ω := by sorry
