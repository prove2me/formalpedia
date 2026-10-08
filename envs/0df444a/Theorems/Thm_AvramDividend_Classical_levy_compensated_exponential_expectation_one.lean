-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_expectation_one
-- name    : AvramDividend.Classical.levy_compensated_exponential_expectation_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:22:18.001987+00:00
-- url     : https://prove2.me/theorems/9130e704-c1a2-4088-a7e6-69c835c4afd0
-- title:
--   Compensated exponential Lévy process has unit expectation at each deterministic time
-- statement:
--   For every t≥0 and θ≥0, the Laplace-normalised exponential e^(θX_t - tψ(θ)) of the spectrally negative Lévy process has expectation one. This is the deterministic-time normalisation ingredient for constructing exponential Lévy martingales and a subsequent generator-to-martingale/Dynkin calculus bridge.
-- source:
--   Immediate consequence of the defining Laplace transform X.laplace and exponential multiplication laws; prerequisite toward the stochastic-calculus portion of AvramDividend.Classical.local_verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_compensated_exponential_expectation_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ) ∂P) = 1 := by sorry
