-- Prove2me | Theorems.Thm_BertsekasShreve_Monotone_cor5_3_1_finite_state_bellman
-- name    : BertsekasShreve.Monotone.cor5_3_1_finite_state_bellman
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:19:59.946225+00:00
-- url     : https://prove2.me/theorems/19cf06dc-77f2-4e1b-8598-6c1239c8427c
-- title:
--   Corollary 5.3.1 — under D and D.2 with finite S and J* > −∞, J* = T(J*) and J* is the largest such J ≤ J₀
-- statement:
--   In the abstract monotone dynamic programming model (state space $S$, constraint sets $U(x)$, monotone mapping $H$, terminal function $J_0>-\infty$, operator $T(J)(x)=\inf_{u\in U(x)}H(x,u,J)$, policy costs $J_\pi=\lim_N(T_{\mu_0}\cdots T_{\mu_{N-1}})(J_0)$ and optimal cost $J^*=\inf_\pi J_\pi$), assume
--
--   1. Assumption D: $J_0(x)\ge H(x,u,J_0)$ for all $x\in S$, $u\in U(x)$;
--   2. Assumption D.2: for some $\alpha>0$, $H(x,u,J)-\alpha r\le H(x,u,J-r)\le H(x,u,J)$ for all $r>0$, $J\le J_0$, $x\in S$, $u\in U(x)$;
--   3. $S$ is a finite set;
--   4. $J^*(x)>-\infty$ for all $x\in S$.
--
--   Then
--   $$J^* = T(J^*).$$
--   Furthermore, if $J' : S\to[-\infty,\infty]$ satisfies $J'\le J_0$ and $J'\le T(J')$, then $J'\le J^*$.
--
--   This is the version of Proposition 5.3 in which the continuity Assumption D.1 is replaced by D.2 together with finiteness of the state space and finiteness from below of $J^*$.
--
--   **Formalization Note** The model and the assumptions D, D.2 are the published `MonotoneDP.Decrease` definitions; finiteness of $S$ is `[Finite S]`.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 76, Corollary 5.3.1

import Mathlib
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions

namespace BertsekasShreve.Monotone

/-- Bertsekas & Shreve (1996), p. 76, Corollary 5.3.1: let D and D.2 hold, let `S` be a finite set,
and let `J*(x) > −∞` for all `x ∈ S`. Then `J* = T(J*)`; furthermore every `J' ∈ F` with
`J' ≤ J₀` and `J' ≤ T(J')` satisfies `J' ≤ J*`. -/
theorem cor5_3_1_finite_state_bellman {S C : Type*} [Finite S]
    (m : MonotoneDP.Decrease.Model S C)
    (hD : m.AssumptionD) (hD2 : ∃ α : ℝ, m.AssumptionD2 α) (hfin : ∀ x : S, ⊥ < m.Jstar x) :
    m.Jstar = m.T m.Jstar ∧
      ∀ J' : S → EReal, J' ≤ m.Jbar → J' ≤ m.T J' → J' ≤ m.Jstar := by sorry

end BertsekasShreve.Monotone
