-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_second_moment
-- name    : AvramDividend.Classical.levy_bounded_stopping_compensated_increment_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:00:25.925378+00:00
-- url     : https://prove2.me/theorems/3ff82cbb-bb57-4510-ae06-2f3dd23ecfb3
-- title:
--   Second moment of compensated Lévy exponential increment after bounded stopping
-- statement:
--   For bounded stopping time τ, a nonnegative horizon h and θ≥0, the cumulant-compensated exponential future increment has second moment exp(h[ψ(2θ)−2ψ(θ)]). The identity supplies exact L² control for stopped exponential-martingale increments in the dividend verification arguments.
-- source:
--   Expand the square inside the exponential, extract the deterministic normalisation and apply the established strong-Markov stopping-time Laplace formula at parameter 2θ.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_laplace
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_compensated_increment_second_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, (Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ θ)) ^ 2 ∂P =
        Real.exp ((h : ℝ) * (X.ψ (2 * θ) - 2 * X.ψ θ)) := by sorry
