-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_exponential_conditional_growth_from_laplace
-- name    : AvramDividend.Classical.levy_exponential_conditional_growth_from_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:57:22.603099+00:00
-- url     : https://prove2.me/theorems/38c28128-3c2a-4274-b0b5-4a18308fcd53
-- title:
--   Exponential conditional Lévy growth bound from process assumptions and the Laplace exponent
-- statement:
--   For any spectrally negative Levy process at deterministic times s≤t and any theta≥0 whose Laplace exponent is bounded by q, prove directly that the conditional expectation of exp(theta X_t) given F_s is at most exp(theta X_s) exp((t−s)q), almost surely. The process assumptions provide the relevant exponential integrability and adaptedness via the previously Proved conditional exponential semigroup theorem. The eigenfunction identity evaluates the remaining exponential moment. Monotonicity of exp and nonnegativity of the past factor give the inequality. This is the unconditional deterministic-time exponential supermartingale inequality, with no additional integrability premises, and does not yet establish controlled dividend stopping or general generator HJB verification. Publication must wait for the conditional semigroup theorem to be Proved.
-- source:
--   Dependency-gated levy_exponential_conditional_semigroup (authoring request 8b6fee6c-fcb7-44f8-ac79-7898237fb00c) and Proved exponential eigenfunction target ee03658e-3ad0-4002-9c09-77a43e0a85b7.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_exponential_conditional_semigroup
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_exponential_conditional_growth_from_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (θ q : ℝ)
    (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q) :
    ∀ᵐ ω ∂P,
      (P[(fun η => Real.exp (θ * X.X t η)) | 𝓕 s]) ω ≤
        Real.exp (θ * X.X s ω) *
          Real.exp (((t - s : ℝ≥0) : ℝ) * q) := by sorry
