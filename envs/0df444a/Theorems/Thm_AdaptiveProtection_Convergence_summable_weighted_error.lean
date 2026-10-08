-- Prove2me | Theorems.Thm_AdaptiveProtection_Convergence_summable_weighted_error
-- name    : AdaptiveProtection.Convergence.summable_weighted_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:08:24.55599+00:00
-- url     : https://prove2.me/theorems/f4206597-1192-4ba8-8759-e6efd49c76db
-- title:
--   Proof of Theorem 1, p. 766 — if (10) holds for class i, then Σ_n γ_n|θ^n_i − θ*_i| < ∞ (a.s.)
-- statement:
--   Assume fares $f_1 > \cdots > f_{k+1} > 0$, independent nonnegative class demands with bounded support (A1), step sizes $\gamma_n = A/(n+B)$ with $A > 0$, $B \ge 0$, and let $\theta^n$ follow the recursion (4) from an arbitrary $\theta^1$. Fix a vector $\theta^*$, a class $1 \le i \le k$, and constants $\beta > 0$ and $C$ such that the rate (10) holds for class $i$:
--   $$E|\theta^n_i - \theta^*_i|^2 \le C\gamma_n^{\beta/2^{i-1}} \qquad (n \ge 1).$$
--   Then
--   $$\sum_n \gamma_n |\theta^n_i - \theta^*_i| < +\infty \quad \text{almost surely.}$$
--
--   This shows that the last term of (12) is summable, which is what the Robbins–Siegmund lemma requires in the induction step of Theorem 1.
--
--   **Formalization Note** Lean's index $n$ is the paper's $n + 1$: the iterate `iterate … n` is paired with `stepSize A B (n + 1)`. The rate hypothesis is stated as in the conclusion of the goal theorem, together with integrability of the squared error, so that the Bochner integral is the genuine expectation (a non-integrable function would have integral $0$ and satisfy the bound vacuously). Under A1 the iterates are bounded (Lemma 3), so this integrability holds anyway.
-- source:
--   van Ryzin & McGill, Management Science 46(6), 2000, p. 766, proof of Theorem 1, paragraph after (12) (left column)

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model
import Definitions.Def_AdaptiveProtection_Convergence_Setting

open MeasureTheory Filter Topology

namespace AdaptiveProtection.Convergence

/-- The summability claim in the proof of Theorem 1 (p. 766): if the rate (10) holds for class `i`
(in the form of the goal's conclusion, with integrability of the squared error), then `∑_n γ_n |θ^n_i − θ*_i| < ∞` a.s. (Lean's index `n` is the paper's `n + 1`). -/
theorem summable_weighted_error
    (k : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 1 ≤ i → i ≤ k → f (i + 1) < f i) (hfpos : 0 < f (k + 1))
    (ν : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hnonneg : ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ᵐ t ∂(ν i), 0 ≤ t)
    (A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B)
    (θ₁ θstar : ℕ → ℝ)
    (hA1 : ∃ Cb : ℝ, ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ᵐ t ∂(ν i), t < Cb)
    (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k)
    (β C : ℝ) (hβ : 0 < β)
    (hrate : ∀ n : ℕ,
      Integrable (fun ω => (iterate f k (stepSize A B) θ₁ ω n i - θstar i) ^ 2) (pathLaw ν) ∧
      ∫ ω, (iterate f k (stepSize A B) θ₁ ω n i - θstar i) ^ 2 ∂(pathLaw ν)
        ≤ C * stepSize A B (n + 1) ^ (β / 2 ^ (i - 1))) :
    ∀ᵐ ω ∂(pathLaw ν), Summable fun n =>
      stepSize A B (n + 1) * |iterate f k (stepSize A B) θ₁ ω n i - θstar i| := by sorry

end AdaptiveProtection.Convergence
