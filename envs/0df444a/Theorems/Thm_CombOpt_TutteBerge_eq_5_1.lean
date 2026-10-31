-- Prove2me | Theorems.Thm_CombOpt_TutteBerge_eq_5_1
-- name    : CombOpt.TutteBerge.eq_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:07:53.102991+00:00
-- url     : https://prove2.me/theorems/9b084e0c-bea8-4c58-bdf9-d31ef345a51c
-- title:
--   (5.1), p. 130 — $\nu(G)\le\tfrac12(|V|-\mathrm{oc}(G\setminus A)+|A|)$
-- statement:
--   For every finite graph $G=(V,E)$ and every $A\subseteq V$,
--   $$
--   \nu(G)\le\tfrac12\bigl(|V|-\mathrm{oc}(G\setminus A)+|A|\bigr).
--   $$
--   This is the easy half of the Tutte–Berge formula. Each set $A$ certifies an upper bound on the size of every matching, and the bound is at least as strong as the bound given by a node cover.
--
--   Differences from the source:
--   - reading: a matching is a set of edges such that no node is incident with more than one of them (p. 127) → IsMatching also requires that no edge of M is a loop; reason: the book's next sentences say M covers exactly 2|M| nodes and leaves |V| − 2|M| exposed, which fails for a loop
--   - encoding: |V|, |M|, |A| for finite sets → Nat.card V and Set.ncard, with binders [Finite V] [Finite E]; reason: these are the true cardinalities of finite sets
--   - encoding: ½(·) and (|V(C)| − 1)/2 on integers → the expression in ℚ after casting every cardinal; reason: no truncation; the value of the book's expression
--   - encoding: oc(H), the number of odd components of H; G\A → odd connected components of H.toSimple (distinct nodes adjacent iff some edge joins them); G\A on the node and edge subtypes outside A; reason: loops and parallel edges do not change which nodes are joined by a path, so the components are the book's
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, (5.1), p. 130 (PDF p. 138)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_matchingNumber
import Definitions.Def_CombOpt_TutteBerge_Multigraph_tutteBergeBound

namespace CombOpt.TutteBerge

/-- **Inequality (5.1).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), (5.1), p. 130 (PDF p. 138): "For any A ⊆ V, ν(G) ≤ ½(|V| − oc(G\A) + |A|)." -/
theorem eq_5_1 {V E : Type*} [Finite V] [Finite E] (G : Multigraph V E) (A : Set V) :
    (G.matchingNumber : ℚ) ≤ G.tutteBergeBound A := by sorry

end CombOpt.TutteBerge
