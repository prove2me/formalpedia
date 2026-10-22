-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_exponential_conditional_growth_bound
-- name    : AvramDividend.Classical.levy_exponential_conditional_growth_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:42:48.726951+00:00
-- url     : https://prove2.me/theorems/c7d9ceab-7ebb-44f8-b3ce-0d80af276d26
-- title:
--   Exponential Lévy conditional growth bound under the Laplace-discount inequality
-- statement:
--   For a spectrally negative Levy process and s≤t, theta≥0, and Laplace exponent psi(theta)≤q, assume the integrability and adapted past exponential factor conditions of the conditional exponential factorisation theorem. Then the conditional expectation of exp(theta X_t) given F_s is bounded almost surely by exp(theta X_s) exp((t−s)q). Combine the accepted exponential transition eigenfunction with the separately published conditional exponential factorisation and monotonicity of the ordinary exponential. This is the deterministic-time discounted supermartingale step for an exponential test function. The result does not assert optional stopping, arbitrary C² generator identity or the controlled dividend HJB inequality. This publication depends on authoritative Proved status of the conditional factorisation theorem; do not publish before that status.
-- source:
--   Dependency-gated levy_exponential_condExp_factorization, authoring request 3f3c1c3a-9d75-4218-baa2-2f17058571b7, and already Proved levy_transition_exponential_eigenfunction ee03658e-3ad0-4002-9c09-77a43e0a85b7.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_exponential_condExp_factorization
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_exponential_conditional_growth_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (θ q : ℝ)
    (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
    (hPast : StronglyMeasurable[𝓕 s]
      (fun ω => Real.exp (θ * X.X s ω)))
    (hTotal : Integrable (fun ω => Real.exp (θ * X.X t ω)) P)
    (hIncrement : Integrable
      (fun ω => Real.exp (θ * (X.X t ω - X.X s ω))) P)
    (hDet : Integrable
      (fun ω => Real.exp (θ * X.X (t - s) ω)) P) :
    ∀ᵐ ω ∂P,
      (P[(fun η => Real.exp (θ * X.X t η)) | 𝓕 s]) ω ≤
        Real.exp (θ * X.X s ω) *
          Real.exp (((t - s : ℝ≥0) : ℝ) * q) := by sorry
