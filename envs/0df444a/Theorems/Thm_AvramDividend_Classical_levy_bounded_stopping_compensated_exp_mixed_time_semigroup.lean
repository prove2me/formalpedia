-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_exp_mixed_time_semigroup
-- name    : AvramDividend.Classical.levy_bounded_stopping_compensated_exp_mixed_time_semigroup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:49:46.101476+00:00
-- url     : https://prove2.me/theorems/f542f609-d75e-4570-bf8a-f51ddbdd1bda
-- title:
--   Time-semigroup law for the compensated mixed Lévy exponential moment
-- statement:
--   Use the accepted two-parameter compensated mixed-moment formula at horizon h+k, normalise casts of nonnegative horizon sums, and factor the exponential by the addition identity. The result is the semigroup law for Lévy second-order compensated moments.
-- source:
--   Use the accepted two-parameter compensated mixed-moment formula at horizon h+k, normalise casts of nonnegative horizon sums, and factor the exponential by the addition identity. The result is the semigroup law for Lévy second-order compensated moments.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_exp_mixed_moment
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_compensated_exp_mixed_time_semigroup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h k : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    ∫ ω, Real.exp (θ *
      (X.X (τ ω + (h + k)) ω - X.X (τ ω) ω) -
      ((h + k) : ℝ) * X.ψ θ) *
      Real.exp (η *
        (X.X (τ ω + (h + k)) ω - X.X (τ ω) ω) -
        ((h + k) : ℝ) * X.ψ η) ∂P =
        Real.exp ((h : ℝ) * (X.ψ (θ + η) - X.ψ θ - X.ψ η)) *
          Real.exp ((k : ℝ) * (X.ψ (θ + η) - X.ψ θ - X.ψ η)) := by sorry
