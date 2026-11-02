-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_clock_piecewise_terminal_nonnegative
-- name    : AvramDividend.Classical.avram_wave6_06_original_zero_clock_piecewise_terminal_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:36:14.279205+00:00
-- url     : https://prove2.me/theorems/9bd8e442-85b4-48e7-9612-878113303984
-- title:
--   Actual source zero-clock corrected piecewise terminal under BV C1 and UBV C2
-- statement:
--   For original X and original admissible D and any τ, the exact source corrected piecewise W uses x+X_tau-rightLimit D_tau when τ=0 OR τ<ruinTime; otherwise original book riskProcess. The OR-at-zero is indispensable: initial dividend atom belongs to paymentTimes even when ruinTime=0, so prepayment terminal would double count cash. Under w(0)>=0, zero extension below 0, positive cap, original BV C1/UBV C2 smoothness and derivative floor, show exp(-qτ)w(W)≥0 a.e. by accepted original BV and UBV postpayment and all-time book-terminal sign results. This is a terminal sign, not a stopped Ito chain rule.
-- source:
--   Source Proposition 4(i) (5.11)-(5.13) dividend time-zero convention. Corrects Chat06 terminal selection for τ=ruinTime=0. Imports Proved original BV C1/UBV C2 postpayment and book terminal sign.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_book_reserve_terminal_nonnegative_separate_gradient

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_06_original_zero_clock_piecewise_terminal_nonnegative
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
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ᵐ ω ∂P, 0 ≤ Term ω := by sorry
