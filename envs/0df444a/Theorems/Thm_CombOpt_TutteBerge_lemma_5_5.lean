-- Prove2me | Theorems.Thm_CombOpt_TutteBerge_lemma_5_5
-- name    : CombOpt.TutteBerge.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:09.383881+00:00
-- url     : https://prove2.me/theorems/e74ed2d1-3a84-4165-86d7-ff3c2769ee95
-- title:
--   Lemma 5.5 — two inessential neighbours lie on a tight odd circuit
-- statement:
--   Let $G=(V,E)$ be a finite graph and let $vw\in E$. If $v$ and $w$ are both inessential, then there is a tight odd circuit $C$ using $vw$. Moreover, $C$ is an inessential node of $G\times C$.
--
--   The lemma is what makes shrinking lossless where it is needed: it produces a circuit along which the matching number is exactly controlled.
--
--   **Formalization Note** The case $v=w$, where $vw$ is a loop, is included. A loop is an odd circuit of length $1$.
--
--   Differences from the source:
--   - reading: a matching is a set of edges such that no node is incident with more than one of them (p. 127) → IsMatching also requires that no edge of M is a loop; reason: the book's next sentences say M covers exactly 2|M| nodes and leaves |V| − 2|M| exposed, which fails for a loop
--   - encoding: |V|, |M|, |A| for finite sets → Nat.card V and Set.ncard, with binders [Finite V] [Finite E]; reason: these are the true cardinalities of finite sets
--   - encoding: ½(·) and (|V(C)| − 1)/2 on integers → the expression in ℚ after casting every cardinal; reason: no truncation; the value of the book's expression
--   - encoding: the new node C of G × C; edges of G × C as edges of G → the node none of Option {v // v ∉ V(C)}; the subtype of edges outside γ(V(C)), with Subtype.val; reason: same graph; the book's edges keep their identity
--   - encoding: an edge vw ∈ E → an edge e with G.ends e = s(v, w); reason: the book's notation for an edge with ends v, w; parallel edges are distinguished
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Lemma 5.5, p. 133 (PDF p. 141)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_IsInessential
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_edgeSet
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_nodeSet
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_IsTight
import Definitions.Def_CombOpt_TutteBerge_Multigraph_shrink

namespace CombOpt.TutteBerge

/-- **Lemma 5.5.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Lemma 5.5, p. 133 (PDF p. 141): "Let G = (V, E) be a graph and let vw ∈ E. If v, w are both
inessential, then there is a tight odd circuit C using vw. Moreover, C is an inessential node of
G × C."

`e` is the edge vw, and `none` is the new node C of `G × C`. `IsTight` includes that `C` is an odd
circuit. The case `v = w` (a loop) is not excluded. -/
theorem lemma_5_5 {V E : Type*} [Finite V] [Finite E] (G : Multigraph V E) {v w : V} (e : E)
    (he : G.ends e = s(v, w)) (hv : G.IsInessential v) (hw : G.IsInessential w) :
    ∃ (x : V) (C : G.Path x x), C.IsTight ∧ e ∈ C.edgeSet ∧
      (G.shrink C.nodeSet).IsInessential none := by sorry

end CombOpt.TutteBerge
