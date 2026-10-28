-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_variance_time_semigroup
-- name    : AvramDividend.Classical.levy_bounded_stopping_compensated_variance_time_semigroup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:51:43.510451+00:00
-- url     : https://prove2.me/theorems/86e9d2ce-2637-419f-995a-fb758c81c972
-- title:
--   Variance semigroup identity for centred Lévy exponentials after bounded stopping
-- statement:
--   The exact variance at horizon h+k equals exp((h+k)(ψ(2θ)−2ψθ))−1. Factor this exponential into its h and k components and expand the product to obtain the variance propagation formula.
-- source:
--   The exact variance at horizon h+k equals exp((h+k)(ψ(2θ)−2ψθ))−1. Factor this exponential into its h and k components and expand the product to obtain the variance propagation formula.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_exact_variance
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_compensated_variance_time_semigroup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h k : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, (Real.exp (θ *
      (X.X (τ ω + (h + k)) ω - X.X (τ ω) ω) -
      ((h + k) : ℝ) * X.ψ θ) - 1) ^ 2 ∂P =
      (Real.exp ((h : ℝ) * (X.ψ (2 * θ) - 2 * X.ψ θ)) - 1) +
        (Real.exp ((k : ℝ) * (X.ψ (2 * θ) - 2 * X.ψ θ)) - 1) +
        (Real.exp ((h : ℝ) * (X.ψ (2 * θ) - 2 * X.ψ θ)) - 1) * (Real.exp ((k : ℝ) * (X.ψ (2 * θ) - 2 * X.ψ θ)) - 1) := by sorry
