-- Prove2me | Theorems.Thm_BertsekasShreve_FiniteHorizon_minimax_dp_eps_optimal
-- name    : BertsekasShreve.FiniteHorizon.minimax_dp_eps_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:38:39.587212+00:00
-- url     : https://prove2.me/theorems/95f10807-fc3f-483d-beee-e5e33ebeb2fb
-- title:
--   Corollary 3.7.1(a) — finite-horizon minimax control: J*_N = T^N(0) and N-stage ε-optimal policies exist
-- statement:
--   Let $(S,C,U,H)$ be a model whose mapping is the minimax mapping (34) of Section 2.3.5, with $W(x,u)\ne\emptyset$ for $x\in S$, $u\in U(x)$ and $\alpha>0$, and let $J_0(x)=0$ for all $x\in S$. Let $N\ge1$. If $J^*_k(x)>-\infty$ for all $x\in S$ and $k=1,2,\dots,N$, then
--   $$J^*_N=T^N(J_0),$$
--   and for each $\varepsilon>0$ there exists an $N$-stage $\varepsilon$-optimal policy.
--
--   This is the finite-horizon minimax control problem (equivalently, a sequential zero-sum game against nature) solved by the dynamic programming recursion.
--
--   **Formalization Note** Only part (a) of the corollary is stated; part (b) says that Propositions 3.3, 3.4 and Corollary 3.3.1 apply, which needs no separate statement since those results hold for every model.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 51, Corollary 3.7.1(a)

import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Problem
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels

namespace BertsekasShreve.FiniteHorizon

open Model

/-- Corollary 3.7.1(a) (Bertsekas & Shreve 1996, p. 51). Let `m` be a model whose mapping is the
minimax mapping (34) of Section 2.3.5 (with `W(x, u)` nonempty for `u ∈ U(x)` and `α > 0`), and
let `J₀(x) = 0` for all `x ∈ S`. If `J*_k(x) > −∞` for all `x ∈ S`, `k = 1, 2, …, N`, then
`J*_N = T^N(J₀)`, and for each `ε > 0` there exists an `N`-stage `ε`-optimal policy. -/
theorem minimax_dp_eps_optimal {S C W : Type*} (m : Model S C) (Wset : S → C → Set W)
    (g : S → C → W → EReal) (f : S → C → W → S) (α : ℝ) (hα : 0 < α)
    (hW : ∀ x, ∀ u ∈ m.U x, (Wset x u).Nonempty)
    (hH : m.H = minimaxH Wset g f α) (J₀ : S → EReal) (hJ₀ : J₀ = fun _ => 0)
    (N : ℕ) (hN : 1 ≤ N)
    (hfin : ∀ x (k : ℕ), 1 ≤ k → k ≤ N → m.optCostN J₀ k x ≠ ⊥) :
    m.optCostN J₀ N = m.T^[N] J₀ ∧
      ∀ ε : ℝ, 0 < ε → ∃ π : m.Policy, m.IsNStageEpsOptimal J₀ N ε π := by sorry

end BertsekasShreve.FiniteHorizon
