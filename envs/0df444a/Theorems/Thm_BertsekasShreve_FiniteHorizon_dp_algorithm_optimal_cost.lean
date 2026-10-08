-- Prove2me | Theorems.Thm_BertsekasShreve_FiniteHorizon_dp_algorithm_optimal_cost
-- name    : BertsekasShreve.FiniteHorizon.dp_algorithm_optimal_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:38:55.247951+00:00
-- url     : https://prove2.me/theorems/cd0acaaa-dbf3-4832-833a-9aa95ce1e349
-- title:
--   Proposition 3.1 — under F.1 or F.2 the DP algorithm yields J*_N = T^N(J_0); under F.2 N-stage ε-optimal policies exist
-- statement:
--   Let $(S,C,U,H)$ be a model of Section 2.1 (Monotonicity Assumption in force), $J_0\in F$ with $J_0(x)>-\infty$ for all $x\in S$, and $N$ a positive integer. Write $J_{k,\pi}=(T_{\mu_0}\cdots T_{\mu_{k-1}})(J_0)$ and $J^*_k=\inf_{\pi\in\Pi}J_{k,\pi}$.
--
--   1. (a) Let Assumption F.1 hold and assume that $J_{k,\pi}(x)<\infty$ for all $x\in S$, $\pi\in\Pi$ and $k=1,2,\dots,N$. Then
--   $$J^*_N=T^N(J_0).$$
--   2. (b) Let Assumption F.2 hold and assume that $J^*_k(x)>-\infty$ for all $x\in S$ and $k=1,2,\dots,N$. Then $J^*_N=T^N(J_0)$, and for every $\varepsilon>0$ there exists an $N$-stage $\varepsilon$-optimal policy, i.e. a $\pi_\varepsilon\in\Pi$ such that
--   $$J^*_N\le J_{N,\pi_\varepsilon}\le J^*_N+\varepsilon.$$
--
--   This is the basic justification of the dynamic programming algorithm $J_0, T(J_0), T^2(J_0),\dots$ in the abstract setting: the optimal cost over all policies, an infimum over sequences of decision rules, is obtained by $N$ successive one-step minimizations. The book's Counterexamples 1–4 show that neither the continuity assumption nor the finiteness assumptions can be dropped.
--
--   **Formalization Note** $J^*_N$ is an infimum over policies and $T^N$ is the $N$-fold iterate of $T$, so the identity has content. Both parts are stated as one conjunction with their own hypotheses.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, pp. 40–41, Proposition 3.1

import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Problem
import Definitions.Def_BertsekasShreve_FiniteHorizon_Assumptions

namespace BertsekasShreve.FiniteHorizon

open Model

/-- Proposition 3.1 (Bertsekas & Shreve 1996, pp. 40–41). Let `J₀ ∈ F` satisfy
`J₀(x) > −∞` for all `x` (eq. (4) of Chapter 2) and let `N` be a positive integer.
(a) Under F.1, if `J_{k,π}(x) < ∞` for all `x ∈ S`, `π ∈ Π`, `k = 1, …, N`, then
`J*_N = T^N(J₀)`.
(b) Under F.2, if `J*_k(x) > −∞` for all `x ∈ S`, `k = 1, …, N`, then `J*_N = T^N(J₀)` and
for every `ε > 0` there is `π_ε ∈ Π` with `J*_N ≤ J_{N,π_ε} ≤ J*_N + ε`. -/
theorem dp_algorithm_optimal_cost {S C : Type*} (m : Model S C) (J₀ : S → EReal)
    (hJ₀ : ∀ x, J₀ x ≠ ⊥) (N : ℕ) (hN : 1 ≤ N) :
    (m.AssumptionF1 →
      (∀ x (π : m.Policy) (k : ℕ), 1 ≤ k → k ≤ N → m.costN J₀ k π x < ⊤) →
      m.optCostN J₀ N = m.T^[N] J₀) ∧
    (m.AssumptionF2 →
      (∀ x (k : ℕ), 1 ≤ k → k ≤ N → m.optCostN J₀ k x ≠ ⊥) →
      m.optCostN J₀ N = m.T^[N] J₀ ∧
        ∀ ε : ℝ, 0 < ε → ∃ π : m.Policy,
          m.optCostN J₀ N ≤ m.costN J₀ N π ∧
            m.costN J₀ N π ≤ fun x => m.optCostN J₀ N x + (ε : EReal)) := by sorry

end BertsekasShreve.FiniteHorizon
