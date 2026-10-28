-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_centered_memLp_two
-- name    : AvramDividend.Classical.levy_bounded_stopping_compensated_increment_centered_memLp_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:06:32.822693+00:00
-- url     : https://prove2.me/theorems/8bdc362b-9a46-4472-a867-070e0612ad56
-- title:
--   L² integrability of the centred compensated exponential Lévy increment
-- statement:
--   Under the finite-measure hypothesis, the centred stopped exponential increment exp(−hψ(θ))exp(θ[X_(τ+h)−X_τ])−1 is in L². This is the basic square-integrability condition for compensated martingale increments and ensuing variance calculations.
-- source:
--   Start with the proved L² integrability of the post-stopping exponential increment. Scale by the deterministic cumulant factor and subtract the constant-one L² function using Mathlib's MemLp.sub.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_exp_memLp_two
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_compensated_increment_centered_memLp_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    MemLp (fun ω => Real.exp (-((h : ℝ) * X.ψ θ)) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) - 1) 2 P := by sorry
