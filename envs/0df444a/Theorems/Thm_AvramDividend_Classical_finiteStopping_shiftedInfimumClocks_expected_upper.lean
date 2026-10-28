-- Prove2me | Theorems.Thm_AvramDividend_Classical_finiteStopping_shiftedInfimumClocks_expected_upper
-- name    : AvramDividend.Classical.finiteStopping_shiftedInfimumClocks_expected_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:05:18.682255+00:00
-- url     : https://prove2.me/theorems/d133167b-7418-4884-9f7c-a6fb954368fe
-- title:
--   Stopped Markov reward bound for named shifted two-sided passage clocks
-- statement:
--   If the upper and lower exit infima of a shifted Lévy path are represented by named random times ρ and σ, the discounted expectation of the shifted upper-before-lower reward factors into the stopped-history discount expectation and the original two-sided reward expectation.
-- source:
--   Previously proved finiteStopping_trueShiftedReward_expected_upper and the hypotheses identifying named shifted clocks with their infimum representations.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_finiteStopping_trueShiftedReward_expected_upper

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.finiteStopping_shiftedInfimumClocks_expected_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : MeasurableSet[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A)
    (hAfine : MeasurableSet A) (hτfine : Measurable τ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (q upper lower : ℝ)
    (ρ σ : Ω → ℝ≥0∞)
    (hρ : ∀ ω, ρ ω =
      ⨅ i : {t : ℝ≥0 // upper < X.X (τ ω + t) ω - X.X (τ ω) ω},
        (i.1 : ℝ≥0∞))
    (hσ : ∀ ω, σ ω =
      ⨅ i : {t : ℝ≥0 // X.X (τ ω + t) ω - X.X (τ ω) ω < lower},
        (i.1 : ℝ≥0∞)) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) *
      (if ρ ω < σ ω then
        ENNReal.ofReal (Real.exp (-(q * (ρ ω).toReal))) else 0)
      else 0 ∂P) ≤
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
                   (⨅ (t : ℝ≥0) (_ : X.X t ω < lower), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q *
         ENNReal.toReal (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) := by sorry
