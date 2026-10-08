-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_laplace
-- name    : AvramDividend.Classical.levy_bounded_stopping_increment_laplace
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T06:36:48.945984+00:00
-- url     : https://prove2.me/theorems/516fd8e3-ef98-4f7d-9565-5edcc6cb52bc
-- title:
--   Laplace transform of Lévy increments after a bounded stopping time
-- statement:
--   For a spectrally negative Lévy process with adapted càdlàg paths and increments independent of the deterministic-time filtration, a bounded finite stopping time τ has post-τ increments with the usual Lévy Laplace transform. In particular, for h≥0 and θ≥0, E exp(θ[X_(τ+h)-X_τ])=exp(h ψ(θ)). This is a one-dimensional strong-Markov stepping stone for proving the barrier dividend factorisation. An elementary proof approximates τ from above by finite-valued dyadic stopping times, applies the deterministic independent/stationary-increment hypotheses at each dyadic value, and passes to the limit using càdlàg right-continuity and uniform integrability provided by exponential moments at 2θ. It does not assert the full stopped path-functional law and does not assume an unavailable generic strong-Markov axiom.
-- source:
--   Avram, Palmowski, Pistorius (2007), Proposition 1 strong-Markov passage argument. Canonical SpectrallyNegativeLevy structure indepIncrements, stationaryIncrements, rightCont, laplace fields. Mathlib.Probability.Process.Stopping IsStoppingTime definition, confirmed on 8 October 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_bounded_stopping_increment_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P =
      Real.exp ((h : ℝ) * X.ψ θ) := by sorry
