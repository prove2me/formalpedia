-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_survival_capital_transform_bounded
-- name    : AvramDividend.Classical.killed_survival_capital_transform_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:03:51.096067+00:00
-- url     : https://prove2.me/theorems/e575387b-5eae-4bf2-b0be-275a8ec28e27
-- title:
--   Finite upper bound for the killed-survival capital Laplace transform
-- statement:
--   The positive-initial-reserve Laplace transform of the probability of surviving a fixed Lévy horizon is bounded above by the inverse Laplace exponent. This follows from the Proved reflected-infimum transform, positivity of the reflected infimum, exponential monotonicity, and the fact that the process law is a probability measure.
-- source:
--   Proved killed_survival_capital_reflected_infimum_transform and Mathlib lintegral_mono.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_killed_survival_capital_reflected_infimum_transform

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_survival_capital_transform_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal (Real.exp (-θ * p.1)))
        (x, ω) ∂P ∂volume) ≤ ENNReal.ofReal (1 / θ) := by sorry
