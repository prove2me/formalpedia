-- Prove2me | Theorems.Thm_CombOpt_TutteBerge_eq_5_2
-- name    : CombOpt.TutteBerge.eq_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:09:42.740115+00:00
-- url     : https://prove2.me/theorems/b69fce61-a0b8-4b82-9755-1c202e47c3ab
-- title:
--   (5.2), p. 132 — $\nu(G)\ge\nu(G\times C)+(|V(C)|-1)/2$
-- statement:
--   For an odd circuit $C$ of a finite graph $G$,
--   $$
--   \nu(G)\ge\nu(G\times C)+\frac{|V(C)|-1}{2},
--   $$
--   or equivalently $\mathrm{def}(G)\le\mathrm{def}(G\times C)$.
--
--   Equality in the first form is the definition of a tight circuit. Both forms are stated.
--
--   Differences from the source:
--   - reading: a matching is a set of edges such that no node is incident with more than one of them (p. 127) → IsMatching also requires that no edge of M is a loop; reason: the book's next sentences say M covers exactly 2|M| nodes and leaves |V| − 2|M| exposed, which fails for a loop
--   - encoding: |V|, |M|, |A| for finite sets → Nat.card V and Set.ncard, with binders [Finite V] [Finite E]; reason: these are the true cardinalities of finite sets
--   - encoding: ½(·) and (|V(C)| − 1)/2 on integers → the expression in ℚ after casting every cardinal; reason: no truncation; the value of the book's expression
--   - encoding: the new node C of G × C; edges of G × C as edges of G → the node none of Option {v // v ∉ V(C)}; the subtype of edges outside γ(V(C)), with Subtype.val; reason: same graph; the book's edges keep their identity
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, (5.2), p. 132 (PDF p. 140)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_matchingNumber
import Definitions.Def_CombOpt_TutteBerge_Multigraph_deficiency
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_IsOddCircuit
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_nodeSet
import Definitions.Def_CombOpt_TutteBerge_Multigraph_shrink

namespace CombOpt.TutteBerge

/-- **Inequality (5.2).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), (5.2), p. 132 (PDF p. 140): "Proposition 5.4 gives the inequality
ν(G) ≥ ν(G × C) + (|V(C)| − 1)/2, or equivalently, def(G) ≤ def(G × C)."

Both forms are stated. The first is in `ℚ` after casting, so nothing truncates. -/
theorem eq_5_2 {V E : Type*} [Finite V] [Finite E] (G : Multigraph V E) {x : V}
    (C : G.Path x x) (hC : C.IsOddCircuit) :
    ((G.matchingNumber : ℚ) ≥
        ((G.shrink C.nodeSet).matchingNumber : ℚ) + ((C.nodeSet.ncard : ℚ) - 1) / 2) ∧
      G.deficiency ≤ (G.shrink C.nodeSet).deficiency := by sorry

end CombOpt.TutteBerge
