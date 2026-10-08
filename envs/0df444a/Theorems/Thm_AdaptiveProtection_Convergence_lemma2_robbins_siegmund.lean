-- Prove2me | Theorems.Thm_AdaptiveProtection_Convergence_lemma2_robbins_siegmund
-- name    : AdaptiveProtection.Convergence.lemma2_robbins_siegmund
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:37.112373+00:00
-- url     : https://prove2.me/theorems/9f39f2be-ab47-49b5-9548-506ab7b4a656
-- title:
--   Lemma 2, p. 764 (Robbins–Siegmund 1971) — almost-supermartingale convergence
-- statement:
--   Let $(\Omega, \mathcal F, P)$ be a probability space with a filtration $(\mathcal F_n)_{n \ge 0}$. Let $Z_n, B_n, C_n, D_n$ be nonnegative real random variables adapted to $(\mathcal F_n)$, with each $Z_n$ integrable, satisfying for all $n$
--   $$E(Z_{n+1} \mid \mathcal F_n) \le (1 + B_n) Z_n + C_n - D_n \quad \text{a.s.}$$
--   Then almost surely on the event $\{\sum_n B_n < \infty,\ \sum_n C_n < \infty\}$, one has $\sum_n D_n < \infty$ and $Z_n$ converges to a finite limit.
--
--   This is the supermartingale lemma used to prove almost-sure convergence of each protection level in Theorem 1.
--
--   **Formalization Note** Integrability of each $Z_n$ is added so that Lean's conditional expectation is the genuine one (Lean assigns $0$ to the conditional expectation of a non-integrable function); Robbins and Siegmund's statement uses generalized conditional expectations of nonnegative variables, so this is a mild weakening, harmless in the application, where $Z_n$ is bounded. "Finite" is automatic for real-valued variables, and "$Z_n \to Z < \infty$" is convergence to a real limit.
-- source:
--   van Ryzin & McGill, Management Science 46(6), 2000, p. 764, Lemma 2 (citing Robbins and Siegmund 1971)

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model
import Definitions.Def_AdaptiveProtection_Convergence_Setting

open MeasureTheory Filter Topology

namespace AdaptiveProtection.Convergence

/-- Lemma 2 (p. 764; Robbins and Siegmund 1971): if `E(Z_{n+1} | F_n) ≤ (1 + B_n) Z_n + C_n − D_n`
for nonnegative adapted `Z, B, C, D`, then on `{∑ B_n < ∞, ∑ C_n < ∞}`, `∑ D_n < ∞` and `Z_n`
converges to a finite limit, a.s. Here `Z` is assumed integrable, so that the conditional
expectation is the genuine one. -/
theorem lemma2_robbins_siegmund
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m₀) (Z B C D : ℕ → Ω → ℝ)
    (hZm : ∀ n, StronglyMeasurable[ℱ n] (Z n)) (hBm : ∀ n, StronglyMeasurable[ℱ n] (B n))
    (hCm : ∀ n, StronglyMeasurable[ℱ n] (C n)) (hDm : ∀ n, StronglyMeasurable[ℱ n] (D n))
    (hZ0 : ∀ n ω, 0 ≤ Z n ω) (hB0 : ∀ n ω, 0 ≤ B n ω) (hC0 : ∀ n ω, 0 ≤ C n ω)
    (hD0 : ∀ n ω, 0 ≤ D n ω)
    (hZint : ∀ n, Integrable (Z n) μ)
    (hdrift : ∀ n, μ[Z (n + 1) | ℱ n] ≤ᵐ[μ] fun ω => (1 + B n ω) * Z n ω + C n ω - D n ω) :
    ∀ᵐ ω ∂μ, Summable (fun n => B n ω) → Summable (fun n => C n ω) →
      Summable (fun n => D n ω) ∧ ∃ z : ℝ, Tendsto (fun n => Z n ω) atTop (𝓝 z) := by sorry

end AdaptiveProtection.Convergence
