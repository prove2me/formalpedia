-- Prove2me | Theorems.Thm_FlowAllocGames_StrongPoA_flow_ge_cycles_avoiding_s
-- name    : FlowAllocGames.StrongPoA.flow_ge_cycles_avoiding_s
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:15:33.996595+00:00
-- url     : https://prove2.me/theorems/a6f7d98a-4381-408e-8cf5-02be1a20a3b9
-- title:
--   Proof of Theorem 16, p. 30, last display (corrected) — Flow(a) ≥ number of cycles of C(f*) avoiding s
-- statement:
--   Let $\Gamma$ be a flow allocation game with circulation network $G'$ and auxiliary node $s$, let $f^*$ be an optimal circulation of $G'$ with a decomposition $\mathcal C(f^*)$ into cycles of unit flow, and let $\mathbf a$ be a strong equilibrium of the unit-ranking game. Then the total flow of $\mathbf a$ is at least the number of cycles of $\mathcal C(f^*)$ that do not pass through $s$, counted with multiplicity:
--   $$\mathrm{Flow}(\mathbf a)\ \ge \sum_{\substack{C_i\in\mathcal C(f^*)\\ s\notin C_i}}1 .$$
--
--   For games without fixed supplies no cycle passes through $s$, and the bound combines with the first display of the proof to give $\mathrm{Flow}(\mathbf a^*)\le d\cdot\mathrm{Flow}(\mathbf a)$.
--
--   **Formalization Note** The page prints $\mathrm{Flow}(\mathbf a)\ge\sum_{C_i\in\mathcal C(f^*)}1$ over all cycles. That is false as printed: take one node $v$ with $b_v=1$ and no outgoing edges. Then $\mathcal C(f^*)=\{(s,v,s)\}$ while $\mathrm{Flow}(\mathbf a)=0$. For a cycle through $s$ the edge carrying flow may be the auxiliary edge $(s,v)$, which $\mathrm{Flow}$ does not count, and the deviation argument needs every node of the cycle to be a player. The statement keeps exactly the cycles for which the page's argument applies. A cycle avoids $s$ when all its edges are edges of $G$.
-- source:
--   arXiv:1908.01714v3, proof of Theorem 16, p. 30, last display (corrected to cycles avoiding s)

import Mathlib
import Definitions.Def_FlowAllocGames_StrongPoA_Model
import Definitions.Def_FlowAllocGames_StrongPoA_Cycles

namespace FlowAllocGames.StrongPoA

open Game

/-- Proof of Theorem 16, p. 30, last display (arXiv:1908.01714v3), corrected: for an optimal
circulation `x = f*` of `G′` with unit-cycle decomposition `C(f*)`, the total flow of every strong
equilibrium `a` is at least the number of cycles of `C(f*)` that avoid the auxiliary node `s` (the
cycles all of whose edges are edges of `G`), counted with multiplicity. The printed display counts
every cycle of `C(f*)`, which is false when a cycle passes through `s`. -/
theorem flow_ge_cycles_avoiding_s {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : Game V E) (x : ExtFlow V E) (hx : G.IsOptimalCirculation x)
    (Cs : List (List (ExtEdge V E))) (hCs : G.IsUnitCycleDecomposition x Cs)
    (a : FlowAllocGames.StrongEq.Profile E) (ha : G.IsStrongEquilibrium a) :
    (Cs.filter (fun C => C.all Sum.isLeft)).length ≤ G.flow a := by sorry

end FlowAllocGames.StrongPoA
