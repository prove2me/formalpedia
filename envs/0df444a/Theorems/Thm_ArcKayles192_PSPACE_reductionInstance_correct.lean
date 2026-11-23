-- Prove2me | Theorems.Thm_ArcKayles192_PSPACE_reductionInstance_correct
-- name    : ArcKayles192.PSPACE.reductionInstance_correct
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:22:24.24012+00:00
-- url     : https://prove2.me/theorems/5c424934-d72d-4add-9af2-317df6625df7
-- title:
--   Semantic correctness of the explicit Pos CNF to Arc Kayles instance map
-- statement:
--   For every Pos CNF instance $\varphi$, the explicit matrix instance produced by `reductionInstance` has exactly the same winner as the original Pos CNF game:
--   $$
--   \operatorname{posCNF}(\varphi)
--   \quad\Longleftrightarrow\quad
--   \operatorname{arcKayles}(\operatorname{reductionInstance}(\varphi)).
--   $$
--
--   For $m>0$, the map first duplicates one clause if necessary, then encodes $G_{\operatorname{oddPad}(\varphi)}$ using the vertex order $s,t,A,B,V,T,F,Y,Z$. Thus this equivalence is the conclusion of Claims 9 and 10, transported across the vertex relabelling. For $m=0$, both sides are winning: the empty conjunction is a True win and the map returns the one-edge graph.
--
--   **Formalization Note.** The statement includes empty and repeated clauses and the $m=0$ corner case. The graph instance is the published adjacency-matrix representation, and Arc Kayles is evaluated on its full vertex set under normal play.
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.5 (odd-m padding), pp.8–9 Claims 9 and 10, p.9 'We conclude by Claims 9 and 10.' The empty-conjunction and matrix-relabelling steps are made explicit by the formal instance encoding.

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game
import Definitions.Def_ArcKayles192_PSPACE_PosCNF
import Definitions.Def_ArcKayles192_PSPACE_ReductionInstance

/-- **Correctness of the reduction** (Claims 9 and 10, pp.8–9, and the conclusion of Theorem 1,
p.9). True wins the Pos CNF game on `φ` iff the first player wins Arc Kayles on the concrete graph
instance `reductionInstance φ`. -/
theorem ArcKayles192.PSPACE.reductionInstance_correct (φ : ArcKayles192.PSPACE.PosCNF) :
    ArcKayles192.PSPACE.posCNF φ ↔
      ArcKayles192.PSPACE.arcKayles (ArcKayles192.PSPACE.reductionInstance φ) := by sorry
