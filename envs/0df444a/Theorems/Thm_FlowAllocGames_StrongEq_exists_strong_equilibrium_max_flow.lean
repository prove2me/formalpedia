-- Prove2me | Theorems.Thm_FlowAllocGames_StrongEq_exists_strong_equilibrium_max_flow
-- name    : FlowAllocGames.StrongEq.exists_strong_equilibrium_max_flow
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:21.669178+00:00
-- url     : https://prove2.me/theorems/ba0984e8-64da-49b2-88f5-c52ada725610
-- title:
--   Theorem 9, pp. 22–23 — every unit-ranking game has a strong equilibrium that maximizes the total flow
-- statement:
--   Let $\Gamma = (G, (b_v), (c_e))$ be a flow allocation game on a finite directed multigraph with integral supplies and capacities, played with unit-ranking strategies. Then there is a strong equilibrium $\mathbf a$ that maximizes the total amount of flow:
--
--   $$\mathbf a \text{ is a strong equilibrium} \quad\text{and}\quad \mathrm{Flow}(\mathbf a') \le \mathrm{Flow}(\mathbf a) \ \text{ for every unit-ranking profile } \mathbf a'.$$
--
--   Here $\mathrm{Flow}(\mathbf a) = \sum_{e\in E} \hat f_e$ is the total flow of the clearing state of $\mathbf a$, and a strong equilibrium is a unit-ranking profile from which no non-empty coalition has a joint unit-ranking deviation that strictly improves the utility of every member.
--
--   In particular strong equilibria always exist in unit-ranking games, and the price of stability of strong equilibria with respect to $\mathrm{Flow}$ is $1$.
--
--   **Formalization Note.** This is the first sentence of Theorem 9. Its second sentence — the strong equilibrium can be computed in polynomial time and represented in polynomial space — needs a model of computation and is not formalized; the threshold-ranking representation on which it rests is the milestone on threshold profiles. Coalitions are non-empty and deviations must again be unit-ranking, as in the model.
-- source:
--   arXiv:1908.01714v3, Theorem 9, pp. 22–23 (first sentence); proof pp. 23–24

import Mathlib
import Definitions.Def_FlowAllocGames_StrongEq_Model

namespace FlowAllocGames.StrongEq

open Finset

/-- Theorem 9 (arXiv:1908.01714v3, pp. 22–23), first sentence: every unit-ranking game has a strong
equilibrium whose total flow is maximal among all unit-ranking profiles. -/
theorem exists_strong_equilibrium_max_flow {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Game V E) : ∃ a : Profile E, G.IsStrongEquilibrium a ∧
      ∀ a' : Profile E, G.IsUnitRanking a' → G.flow a' ≤ G.flow a := by sorry

end FlowAllocGames.StrongEq
