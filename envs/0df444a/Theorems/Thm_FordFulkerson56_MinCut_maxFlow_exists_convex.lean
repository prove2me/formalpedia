-- Prove2me | Theorems.Thm_FordFulkerson56_MinCut_maxFlow_exists_convex
-- name    : FordFulkerson56.MinCut.maxFlow_exists_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T15:50:35.838316+00:00
-- url     : https://prove2.me/theorems/9a0722cd-37ac-4b00-b2a6-51853dd80e86
-- title:
--   Proof of Theorem 1, p. 400 — a maximal flow exists and the maximal flows form a convex set
-- statement:
--   Let $N$ be a network with finitely many vertices and arcs, source $a$, sink $b$ and positive capacities. Then there is a maximal flow, and the set of all maximal flows is convex:
--   $$\exists f\ \text{maximal},\qquad f_1,f_2\ \text{maximal},\ t\in[0,1]\ \Longrightarrow\ (1-t)f_1+tf_2\ \text{maximal}.$$
--
--   Here a flow is an assignment of non-negative numbers to chains joining $a$ and $b$ whose arc loads respect the capacities, and a maximal flow is a flow of largest value. The set $S$ of arcs saturated by every maximal flow, and the left arcs, are defined from all maximal flows; without existence these objects would be vacuous, and the averaging steps of Lemmas 1–3 rely on convexity.
--
--   **Formalization Note** Flows are functions from finite sets of arcs to $\mathbb R$; convexity is taken in that real vector space.
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), p. 400, proof of Theorem 1, first paragraph

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsFlow

namespace FordFulkerson56.MinCut

theorem maxFlow_exists_convex {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (N : Network V E) :
    (∃ f, IsMaxFlow N f) ∧ Convex ℝ {f : Finset E → ℝ | IsMaxFlow N f} := by sorry

end FordFulkerson56.MinCut
