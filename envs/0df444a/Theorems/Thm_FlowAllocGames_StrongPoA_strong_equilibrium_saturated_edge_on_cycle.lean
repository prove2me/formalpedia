-- Prove2me | Theorems.Thm_FlowAllocGames_StrongPoA_strong_equilibrium_saturated_edge_on_cycle
-- name    : FlowAllocGames.StrongPoA.strong_equilibrium_saturated_edge_on_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:15:25.399332+00:00
-- url     : https://prove2.me/theorems/35ff9f54-06e6-4078-a885-dea4a93e1551
-- title:
--   Proof of Theorem 16, p. 30, second paragraph — in a strong equilibrium every simple cycle of G has a saturated edge
-- statement:
--   Let $\Gamma=(G,(b_v),(c_e))$ be a flow allocation game and $\mathbf a$ a strong equilibrium of its unit-ranking game, with clearing state $\hat f$. Let $e_1,\dots,e_k$ ($k\ge1$) be a simple directed cycle of $G$: each $e_{j+1}$ starts where $e_j$ ends, $e_k$ ends where $e_1$ starts, and the tails of $e_1,\dots,e_k$ are pairwise distinct. Then some edge of the cycle is saturated:
--   $$\exists\, j\in\{1,\dots,k\}:\qquad \hat f_{e_j}=c_{e_j}.$$
--
--   In the proof of Theorem 16 this is the step that ties the cycles of an optimal circulation to the flow of an arbitrary strong equilibrium: each cycle of $G$ forces at least one unit of equilibrium flow on one of its edges.
--
--   **Formalization Note** The paper argues in the game expanded into unit-capacity multi-edges, for a cycle $C_i$ of the decomposition $\mathcal C(f^*)$ whose unit copies all carry no flow. Back in $G$, an unused unit copy of $e$ exists exactly when $\hat f_e<c_e$, and the argument requires every node of the cycle to be a player, so the cycle lies in $G$. The statement is that argument for an arbitrary simple cycle of $G$; the argument does not use that the cycle comes from $\mathcal C(f^*)$.
-- source:
--   arXiv:1908.01714v3, proof of Theorem 16, p. 30, second paragraph

import Mathlib
import Definitions.Def_FlowAllocGames_StrongPoA_Model
import Definitions.Def_FlowAllocGames_StrongPoA_Cycles

namespace FlowAllocGames.StrongPoA

open Game

/-- Proof of Theorem 16, p. 30, second paragraph (arXiv:1908.01714v3), restated in the original
graph: in a strong equilibrium `a` with clearing state `f̂`, every simple directed cycle of `G` has an
edge `e` that is saturated, `f̂_e = c_e`. -/
theorem strong_equilibrium_saturated_edge_on_cycle {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (G : Game V E) (a : FlowAllocGames.StrongEq.Profile E) (ha : G.IsStrongEquilibrium a)
    (cyc : List E) (hne : cyc ≠ []) (hchain : cyc.IsChain (fun e e' => G.head e = G.tail e'))
    (hclosed : ∀ h : cyc ≠ [], G.head (cyc.getLast h) = G.tail (cyc.head h))
    (hsimple : (cyc.map G.tail).Nodup) :
    ∃ e ∈ cyc, G.clearingState a e = G.c e := by sorry

end FlowAllocGames.StrongPoA
