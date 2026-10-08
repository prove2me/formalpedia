-- Prove2me | Theorems.Thm_BertsekasShreve_Monotone_cor5_7_1_finite_state_eps_optimal
-- name    : BertsekasShreve.Monotone.cor5_7_1_finite_state_eps_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:20:10.927916+00:00
-- url     : https://prove2.me/theorems/21552650-f4de-4f3a-8665-f6df69074577
-- title:
--   Corollary 5.7.1 — under D and D.2 with finite S and J* > −∞, ε-optimal policies exist
-- statement:
--   In the abstract monotone dynamic programming model (state space $S$, constraint sets $U(x)$, monotone mapping $H$, terminal function $J_0>-\infty$, policy costs $J_\pi=\lim_N(T_{\mu_0}\cdots T_{\mu_{N-1}})(J_0)$ and optimal cost $J^*=\inf_\pi J_\pi$), assume
--
--   1. Assumption D: $J_0(x)\ge H(x,u,J_0)$ for all $x\in S$, $u\in U(x)$;
--   2. Assumption D.2 holds for some scalar $\alpha>0$;
--   3. $S$ is a finite set;
--   4. $J^*(x)>-\infty$ for all $x\in S$.
--
--   Then for every $\varepsilon>0$ there exists an $\varepsilon$-optimal policy, i.e. a policy $\pi_\varepsilon$ with
--   $$J^*\le J_{\pi_\varepsilon}\le J^*+\varepsilon.$$
--
--   It is the counterpart under Assumption D of the existence of $\varepsilon$-optimal policies under Assumption I (Proposition 5.1 and Proposition 5.6(a)).
--
--   **Formalization Note** The model and the assumptions are the published `MonotoneDP.Decrease` definitions. Because $J^*>-\infty$ is assumed, the book's general $\varepsilon$-optimality convention reduces to the displayed inequality; at states with $J^*(x)=+\infty$ the bound is $+\infty$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 80, Corollary 5.7.1

import Mathlib
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions

namespace BertsekasShreve.Monotone

/-- Bertsekas & Shreve (1996), p. 80, Corollary 5.7.1: let D and D.2 hold, let `S` be a finite set,
and let `J*(x) > −∞` for all `x ∈ S`. Then for every `ε > 0` there is a policy `π_ε` with
`J* ≤ J_{π_ε} ≤ J* + ε`. -/
theorem cor5_7_1_finite_state_eps_optimal {S C : Type*} [Finite S]
    (m : MonotoneDP.Decrease.Model S C)
    (hD : m.AssumptionD) (hD2 : ∃ α : ℝ, m.AssumptionD2 α) (hfin : ∀ x : S, ⊥ < m.Jstar x) :
    ∀ ε : ℝ, 0 < ε → ∃ π : m.Policy,
      m.Jstar ≤ m.Jpi π ∧ m.Jpi π ≤ fun x => m.Jstar x + (ε : EReal) := by sorry

end BertsekasShreve.Monotone
