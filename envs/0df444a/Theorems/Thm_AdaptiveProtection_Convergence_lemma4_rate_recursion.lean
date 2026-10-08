-- Prove2me | Theorems.Thm_AdaptiveProtection_Convergence_lemma4_rate_recursion
-- name    : AdaptiveProtection.Convergence.lemma4_rate_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:49.4125+00:00
-- url     : https://prove2.me/theorems/906e1ba2-0dcd-4beb-9f09-8cb519175f1e
-- title:
--   Lemma 4, pp. 764–765 — u_n = λγ_n^β satisfies u_{n+1} ≥ (1 − 2δγ_n)u_n + Cγ_n^{β+1} for n > n_0
-- statement:
--   Let $\gamma_n = A/(n + B)$ with constants $A > 0$ and $B \ge 0$, and let $\delta > 0$ and $C > 0$. Then there exist $\beta > 0$, a finite $\lambda \ge 0$ and an index $n_0$ such that $u_n = \lambda\gamma_n^{\beta}$ satisfies
--   $$u_{n+1} \ge (1 - 2\delta\gamma_n) u_n + C\gamma_n^{\beta+1} \qquad \text{for all } n > n_0.$$
--
--   In the proof of Theorem 1 this deterministic comparison sequence turns the recursion $E Z_{n+1} \le (1 - 2\gamma_n\delta) E Z_n + C\gamma_n^{1+\beta/2^i}$ into the mean-square rate (10).
--
--   **Formalization Note** Powers are real powers of the positive numbers $\gamma_n$ ($n \ge 1$; $n > n_0 \ge 0$ guarantees $n \ge 1$). The constant $\lambda$ is named `lam`.
-- source:
--   van Ryzin & McGill, Management Science 46(6), 2000, p. 764, Lemma 4 (adapted from Benveniste et al. 1990, Lemma 23); proof pp. 764–765

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model
import Definitions.Def_AdaptiveProtection_Convergence_Setting

open MeasureTheory Filter Topology

namespace AdaptiveProtection.Convergence

/-- Lemma 4 (pp. 764–765): with `γ_n = A/(n + B)`, there are `β > 0`, a finite `λ ≥ 0` and `n₀`
such that `u_n = λ γ_n^β` satisfies `u_{n+1} ≥ (1 − 2δγ_n) u_n + C γ_n^{β+1}` for all `n > n₀`. -/
theorem lemma4_rate_recursion
    (A B δ C : ℝ) (hA : 0 < A) (hB : 0 ≤ B) (hδ : 0 < δ) (hC : 0 < C) :
    ∃ β > 0, ∃ lam : ℝ, 0 ≤ lam ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n →
      (1 - 2 * δ * stepSize A B n) * (lam * stepSize A B n ^ β) + C * stepSize A B n ^ (β + 1)
        ≤ lam * stepSize A B (n + 1) ^ β := by sorry

end AdaptiveProtection.Convergence
