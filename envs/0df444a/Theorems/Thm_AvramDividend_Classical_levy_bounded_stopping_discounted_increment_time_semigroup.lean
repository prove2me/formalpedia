-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_increment_time_semigroup
-- name    : AvramDividend.Classical.levy_bounded_stopping_discounted_increment_time_semigroup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:35:44.191984+00:00
-- url     : https://prove2.me/theorems/b3a5b41e-1551-4032-a324-11f1dd0fc50f
-- title:
--   Discounted time-semigroup law after bounded Lévy stopping
-- statement:
--   For any bounded stopping time τ, successive deterministic horizons h and k, parameter θ≥0 and discount q∈ℝ, the discounted exponential moment over the combined post-stopping horizon is exp(h(ψ(θ)−q)) exp(k(ψ(θ)−q)).
-- source:
--   Use the established discounted Laplace transform at horizon h+k, identify the real-valued sum of nonnegative horizons, and split the exponential of the sum.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_increment_laplace
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_discounted_increment_time_semigroup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h k : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, Real.exp (-(q * ((h + k) : ℝ))) *
      Real.exp (θ * (X.X (τ ω + (h + k)) ω - X.X (τ ω) ω)) ∂P =
        Real.exp ((h : ℝ) * (X.ψ θ - q)) *
          Real.exp ((k : ℝ) * (X.ψ θ - q)) := by sorry
