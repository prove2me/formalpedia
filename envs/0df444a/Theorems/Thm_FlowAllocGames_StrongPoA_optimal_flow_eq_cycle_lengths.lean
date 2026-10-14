-- Prove2me | Theorems.Thm_FlowAllocGames_StrongPoA_optimal_flow_eq_cycle_lengths
-- name    : FlowAllocGames.StrongPoA.optimal_flow_eq_cycle_lengths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:15:31.324968+00:00
-- url     : https://prove2.me/theorems/1e6cbd1f-69c7-49c9-a74d-8cce3c02a80c
-- title:
--   Proof of Theorem 16, p. 30, first display — an optimal circulation yields the optimal total flow, Σ|C_i| − 2Σb_v
-- statement:
--   Let $\Gamma=(G,(b_v),(c_e))$ be a flow allocation game with circulation network $G'$, let $f^*$ be an optimal (integral) circulation of $G'$, and let $\mathcal C(f^*)=(C_1,\dots,C_k)$ be a decomposition of $f^*$ into cycles of unit flow, each of size at most $d$. Then:
--   1. there is a unit-ranking profile $\mathbf a^*$ whose total flow equals the flow of $f^*$ on the edges of $G$, $\mathrm{Flow}(\mathbf a^*)=\sum_{e\in E}f^*_e$, and $\mathbf a^*$ maximizes $\mathrm{Flow}$ over all unit-ranking profiles;
--   2. the total flow of $f^*$ on $G$ is the total cycle size minus twice the total supply,
--   $$\sum_{v\in V}\sum_{e\in E^+(v)}f^*_e=\sum_{C_i\in\mathcal C(f^*)}|C_i|-2\sum_{v\in V}b_v ;$$
--   3. $\sum_{C_i\in\mathcal C(f^*)}|C_i|\le\sum_{C_i\in\mathcal C(f^*)}d$.
--
--   Together these give $\mathrm{Flow}(\mathbf a^*)\le k\,d-2\sum_v b_v\le k\,d$, the upper half of the price of anarchy bound of Theorem 16.
--
--   **Formalization Note** Identity 2 is stated with $2\sum_v b_v$ added to the left-hand side instead of subtracted on the right, to avoid truncated natural-number subtraction. Item 1 restates, for this mission, the fact from the proof of Theorem 9 (p. 23) that the display relies on ("as observed in the proof of Theorem 9").
-- source:
--   arXiv:1908.01714v3, proof of Theorem 16, p. 30, first display; proof of Theorem 9, p. 23, first display

import Mathlib
import Definitions.Def_FlowAllocGames_StrongPoA_Model
import Definitions.Def_FlowAllocGames_StrongPoA_Cycles

namespace FlowAllocGames.StrongPoA

open Game

/-- Proof of Theorem 16, p. 30, first display (arXiv:1908.01714v3), with the fact from the proof of
Theorem 9 (p. 23) it rests on: an optimal circulation `x = f*` of `G′` yields the total flow of an
optimal unit-ranking profile `a*`, and for every decomposition `C(f*)` of `x` into unit-flow cycles of
size at most `d`,
`Flow(a*) = Σ_{e ∈ E} f*_e = Σ_{C_i ∈ C(f*)} |C_i| − 2 Σ_v b_v ≤ Σ_{C_i ∈ C(f*)} d`.
The middle identity is stated with `2 Σ_v b_v` moved to the left (no ℕ subtraction). -/
theorem optimal_flow_eq_cycle_lengths {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : Game V E) (x : ExtFlow V E) (hx : G.IsOptimalCirculation x)
    (Cs : List (List (ExtEdge V E))) (hCs : G.IsUnitCycleDecomposition x Cs)
    (d : ℕ) (hd : ∀ C ∈ Cs, C.length ≤ d) :
    (∃ astar : FlowAllocGames.StrongEq.Profile E, G.IsUnitRanking astar ∧ G.flow astar = ∑ e, x.g e ∧
      ∀ a : FlowAllocGames.StrongEq.Profile E, G.IsUnitRanking a → G.flow a ≤ G.flow astar) ∧
    ∑ e, x.g e + 2 * ∑ v, G.b v = (Cs.map List.length).sum ∧
    (Cs.map List.length).sum ≤ Cs.length * d := by sorry

end FlowAllocGames.StrongPoA
