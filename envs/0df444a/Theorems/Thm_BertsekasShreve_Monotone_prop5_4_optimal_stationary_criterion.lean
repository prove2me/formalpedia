-- Prove2me | Theorems.Thm_BertsekasShreve_Monotone_prop5_4_optimal_stationary_criterion
-- name    : BertsekasShreve.Monotone.prop5_4_optimal_stationary_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:19:36.973353+00:00
-- url     : https://prove2.me/theorems/1490b8bb-a847-4555-a001-77ae31477032
-- title:
--   Proposition 5.4 — a stationary policy is optimal iff T_μ*(J*) = T(J*); pointwise-optimal policies give a stationary optimal one
-- statement:
--   Consider the abstract monotone dynamic programming model $(S,C,U,H,J_0)$: state space $S$, control space $C$, nonempty constraint sets $U(x)\subseteq C$, a mapping $H$ that is monotone in its function argument, and a terminal function $J_0 > -\infty$. For a selector $\mu$ ($\mu(x)\in U(x)$) let $T_\mu(J)(x)=H(x,\mu(x),J)$ and $T(J)(x)=\inf_{u\in U(x)}H(x,u,J)$; for a policy $\pi=(\mu_0,\mu_1,\dots)$ let $J_\pi=\lim_{N\to\infty}(T_{\mu_0}\cdots T_{\mu_{N-1}})(J_0)$, let $J_\mu$ be the cost of the stationary policy $(\mu,\mu,\dots)$, and let $J^*=\inf_\pi J_\pi$.
--
--   Assume Assumptions I, I.1 and I.2 hold. Then:
--
--   1. A stationary policy $(\mu^*,\mu^*,\dots)$ is optimal, i.e. $J_{\mu^*}=J^*$, if and only if
--   $$T_{\mu^*}(J^*) = T(J^*).$$
--   2. If for each $x\in S$ there exists a policy $\pi_x$ which is optimal at $x$, i.e. $J_{\pi_x}(x)=J^*(x)$, then there exists a stationary optimal policy.
--
--   Part 1 reduces the existence of an optimal stationary policy to attainment of the infimum in Bellman's equation $J^*(x)=\inf_{u\in U(x)}H(x,u,J^*)$ at every state. Part 2 shows that the optimal policies, possibly different from state to state, can always be merged into a single stationary one.
--
--   **Formalization Note** The model and the assumptions are the published `MonotoneDP.Increase` definitions; "I.2 holds" is the existence of a scalar $\alpha$ with `AssumptionI2 α`. Part 2 is the book's formulation (a policy optimal at each state); a policy optimal at all states at once is a special case.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 78, Proposition 5.4, Eq. (18) of Chapter 5

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions

namespace BertsekasShreve.Monotone

/-- Bertsekas & Shreve (1996), p. 78, Proposition 5.4: let I, I.1 and I.2 hold. A stationary policy
`(μ*, μ*, …)` is optimal (`J_{μ*} = J*`) if and only if `T_{μ*}(J*) = T(J*)` (eq. (18)).
Furthermore, if for each `x ∈ S` there exists a policy which is optimal at `x`
(`J_π(x) = J*(x)`), then there exists a stationary optimal policy. -/
theorem prop5_4_optimal_stationary_criterion {S C : Type*} (m : MonotoneDP.Increase.Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    (∀ μ : m.Selector, m.Jmu μ = m.Jstar ↔ m.Tmu μ m.Jstar = m.T m.Jstar) ∧
      ((∀ x : S, ∃ π : m.Policy, m.Jpi π x = m.Jstar x) →
        ∃ μ : m.Selector, m.Jmu μ = m.Jstar) := by sorry

end BertsekasShreve.Monotone
