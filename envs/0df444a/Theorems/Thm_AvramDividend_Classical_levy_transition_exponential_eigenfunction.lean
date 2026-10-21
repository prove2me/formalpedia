-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction
-- name    : AvramDividend.Classical.levy_transition_exponential_eigenfunction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T22:02:00.236604+00:00
-- url     : https://prove2.me/theorems/ee03658e-3ad0-4002-9c09-77a43e0a85b7
-- title:
--   Exponential test payoffs are exact eigenfunctions of the Lévy transition semigroup
-- statement:
--   For the actual spectrally negative Lévy process, every nonnegative Laplace parameter θ, time t≥0 and starting reserve x, the transition expectation E[exp(θ(x+X_t))] equals exp(θx) exp(t ψ(θ)), where ψ(θ)=laplaceExponent X.c X.σ X.ν θ is the recorded Lévy–Khintchine exponent. The source property X.laplace already supplies the exponential moment and equality for X_t. Factor exp(θ(x+X_t)) = exp(θx)exp(θX_t) pointwise and pull the deterministic factor from the integral. This identifies a concrete semigroup eigenfunction of the given process, and is a first test-function case for establishing that the recorded Γ generator matches its semigroup. It does not yet prove Γ for arbitrary C² verification functions, nor the controlled stopped stochastic HJB budget.
-- source:
--   Uses only authoritative SpectrallyNegativeLevy.laplace and pinned real exponential/integral_const_mul lemmas; no Open theorem imports.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_transition_exponential_eigenfunction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) :
    (∫ ω, Real.exp (θ * (x + X.X t ω)) ∂P) =
      Real.exp (θ * x) *
        Real.exp ((t : ℝ) * laplaceExponent X.c X.σ X.ν θ) := by sorry
