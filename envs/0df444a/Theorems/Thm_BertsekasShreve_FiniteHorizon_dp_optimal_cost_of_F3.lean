-- Prove2me | Theorems.Thm_BertsekasShreve_FiniteHorizon_dp_optimal_cost_of_F3
-- name    : BertsekasShreve.FiniteHorizon.dp_optimal_cost_of_F3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:38:41.049094+00:00
-- url     : https://prove2.me/theorems/7032e104-54b0-4afd-ac63-e782fc4479ab
-- title:
--   Proposition 3.2 — under F.3, J*_N = T^N(J_0) and nearly optimal policies exist with dominated convergence
-- statement:
--   Let $(S,C,U,H)$ be a model satisfying Assumption F.3, $J_0\in F$ with $J_0(x)>-\infty$ for all $x$, $N\ge1$, and assume $J_{k,\pi}(x)<\infty$ for all $x\in S$, $\pi\in\Pi$ and $k=1,\dots,N$. Then:
--
--   1. $$J^*_N=T^N(J_0);$$
--   2. if $\{\varepsilon_n\}$ is a sequence of positive numbers with $\varepsilon_n\downarrow0$, there exists a sequence of policies $\{\pi_n\}$ exhibiting $\{\varepsilon_n\}$-dominated convergence to optimality;
--   3. if in addition $J^*_N(x)>-\infty$ for all $x\in S$, then for every $\varepsilon>0$ there exists an $N$-stage $\varepsilon$-optimal policy.
--
--   Unlike Proposition 3.1(b), this result allows $J^*_k$ to take the value $-\infty$, and it is the form that applies to the stochastic model of Section 2.3.3.
--
--   **Formalization Note** The book's last sentence says "an $\varepsilon$-optimal policy"; in this finite-horizon proposition it is the $N$-stage notion (the infinite-horizon cost $J_\pi$ is not defined under its hypotheses), and that is what is stated. "$\varepsilon_n\downarrow0$" is `Antitone ε` together with `ε n → 0`, with $\varepsilon_n>0$ for every index.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 43, Proposition 3.2

import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Problem
import Definitions.Def_BertsekasShreve_FiniteHorizon_Assumptions

namespace BertsekasShreve.FiniteHorizon

open Filter Topology Model

/-- Proposition 3.2 (Bertsekas & Shreve 1996, p. 43). Let F.3 hold, `J₀(x) > −∞` for all `x`,
`N ≥ 1`, and `J_{k,π}(x) < ∞` for all `x ∈ S`, `π ∈ Π`, `k = 1, …, N`. Then
`J*_N = T^N(J₀)`; for every sequence of positive numbers `ε_n ↓ 0` there is a sequence of
policies exhibiting `{ε_n}`-dominated convergence to optimality; and if in addition
`J*_N(x) > −∞` for all `x`, then for every `ε > 0` there is an `N`-stage `ε`-optimal policy. -/
theorem dp_optimal_cost_of_F3 {S C : Type*} (m : Model S C) (J₀ : S → EReal)
    (hJ₀ : ∀ x, J₀ x ≠ ⊥) (N : ℕ) (hN : 1 ≤ N) (hF3 : m.AssumptionF3)
    (hfin : ∀ x (π : m.Policy) (k : ℕ), 1 ≤ k → k ≤ N → m.costN J₀ k π x < ⊤) :
    m.optCostN J₀ N = m.T^[N] J₀ ∧
    (∀ ε : ℕ → ℝ, (∀ n, 0 < ε n) → Antitone ε → Tendsto ε atTop (𝓝 0) →
      ∃ πs : ℕ → m.Policy, m.IsDominatedConvergence J₀ N ε πs) ∧
    ((∀ x, m.optCostN J₀ N x ≠ ⊥) →
      ∀ ε : ℝ, 0 < ε → ∃ π : m.Policy, m.IsNStageEpsOptimal J₀ N ε π) := by sorry

end BertsekasShreve.FiniteHorizon
