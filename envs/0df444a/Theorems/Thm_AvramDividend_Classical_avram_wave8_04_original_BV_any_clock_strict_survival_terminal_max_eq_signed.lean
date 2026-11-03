-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_any_clock_strict_survival_terminal_max_eq_signed
-- name    : AvramDividend.Classical.avram_wave8_04_original_BV_any_clock_strict_survival_terminal_max_eq_signed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:35:13.554296+00:00
-- url     : https://prove2.me/theorems/331f6956-2529-4e5e-9411-07bbe95a15eb
-- title:
--   Original BV every random clock strict-survival positive terminal equals the signed postpayment value, including zero clock
-- statement:
--   The exact positive-part stopped terminal of any original source random clock equals the signed terminal pathwise before ruin, with no stopping-time or measurability assumption. For τ=0, capped initial postpayment reserve lies in [0,C]; for τ>0, capped strictly-before-ruin postpayment reserve lies there. The BV full-cap HJB gradient secant yields nonnegative candidate and positive discount. Supports localisation including clocks attaining zero and all horizon rightpayments.
-- source:
--   Avram Proposition 4(i), pathwise terminal positivity under the original capped dividend strategy, arbitrary finite random clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_04_original_BV_any_clock_strict_survival_terminal_max_eq_signed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) :
    ∀ ω,
      (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
       else 0) =
      (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)
       else 0) := by sorry
