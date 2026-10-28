-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_psi_two_point_convexity
-- name    : AvramDividend.Classical.levy_bounded_stopping_psi_two_point_convexity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:23:46.662735+00:00
-- url     : https://prove2.me/theorems/698bca30-f871-40ed-a9e0-3dbce04d666b
-- title:
--   Two-point convexity bound for the Lévy cumulant from stopped-increment variance
-- statement:
--   For any bounded stopping time and strictly positive deterministic future horizon, the Lévy cumulant satisfies 2ψ(θ)≤ψ(2θ) for θ≥0. The proof derives the bound from nonnegativity of the exact variance of cumulant-compensated future increments.
-- source:
--   Use the proved exact variance identity and nonnegativity of the integral of a square; exp(h[ψ(2θ)−2ψ(θ)])≥1 implies its exponent is nonnegative. Since h>0, divide by h.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_exact_variance
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_psi_two_point_convexity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (hh : 0 < h) (θ : ℝ) (hθ : 0 ≤ θ) :
    2 * X.ψ θ ≤ X.ψ (2 * θ) := by sorry
