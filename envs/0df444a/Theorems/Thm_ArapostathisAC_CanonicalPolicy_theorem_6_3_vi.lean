-- Prove2me | Theorems.Thm_ArapostathisAC_CanonicalPolicy_theorem_6_3_vi
-- name    : ArapostathisAC.CanonicalPolicy.theorem_6_3_vi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:02:29.305987+00:00
-- url     : https://prove2.me/theorems/795dc012-59ec-4dd4-b5a5-027e575a48c5
-- title:
--   Theorem 6.3 (vi) — with constant ρ*, a canonical policy is sample path average cost optimal
-- statement:
--   Let $(S, A, U, P, c)$ be a controlled Markov process with Borel state and action spaces and $c \in \mathcal M_b(K)$, and let $(\rho, h, \pi^*)$ be a canonical triplet with $\rho(x) = \rho^* \in \mathbb R$ for all $x \in S$. Then $\pi^*$ is sample path average cost optimal: there is a constant $\bar\rho$ such that for every initial law $\mu$,
--   $$\limsup_{N\to\infty}\frac1N\sum_{t=0}^{N-1} c(X_t, A_t) = \bar\rho \qquad \mathcal P^{\pi^*}_\mu\text{-a.s.},$$
--   and for every policy $\pi\in\Pi$ and every initial law $\mu'$ the same limit superior is $\ge \bar\rho$, $\mathcal P^{\pi}_{\mu'}$-a.s.
--
--   Beyond the expected-cost optimality of part (iii), the canonical policy is optimal path by path.
--
--   **Formalization Note.** The paper prints (vi) without a hypothesis on $\rho$; we state it under the hypothesis of (v), $\rho \equiv \rho^*$ constant. Without it (vi) is false: with one action, two absorbing states of costs $0$ and $1$, $\rho = c$ and $h = 0$ form a canonical triplet, but the pathwise average cost is $0$ from one state and $1$ from the other, so no single constant works. The paper's proof of (vi) is the same argument as for (v) and uses the constant $\rho^*$. Initial laws are probability measures on $S$, as in the definition on p. 288.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 318, Theorem 6.3 (vi); definition of sample path AC optimality on p. 288

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalPolicy_CMP
import Definitions.Def_ArapostathisAC_CanonicalPolicy_SamplePath

open MeasureTheory ProbabilityTheory Filter Topology

namespace ArapostathisAC.CanonicalPolicy

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]

/-- Theorem 6.3 (vi), p. 318, under the hypothesis of (v): if `(ρ, h, π*)` is a canonical triplet
with `ρ(x) = ρ* ∈ ℝ` for all `x`, and `c ∈ 𝓜_b(K)`, then `π*` is sample path average cost
optimal. -/
theorem theorem_6_3_vi (M : BorelCMP S A) (hc : CostBounded M) (ρ h : S → ℝ) (πs : Policy M)
    (hcan : IsCanonical M ρ h πs) (ρs : ℝ) (hρ : ∀ x, ρ x = ρs) :
    IsSamplePathOptimal M πs := by sorry

end ArapostathisAC.CanonicalPolicy
