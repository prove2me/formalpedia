-- Prove2me | Theorems.Thm_CombOpt_TutteBerge_tutte_berge_formula
-- name    : CombOpt.TutteBerge.tutte_berge_formula
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:07:31.374546+00:00
-- url     : https://prove2.me/theorems/54f23ec7-f6d8-41b8-80ec-fef3917daf45
-- title:
--   Theorem 5.2 — Tutte–Berge Formula
-- statement:
--   For a finite graph $G=(V,E)$,
--   $$
--   \max\{|M| : M \text{ a matching of } G\}=\min\bigl\{\tfrac12\bigl(|V|-\mathrm{oc}(G\setminus A)+|A|\bigr) : A\subseteq V\bigr\}.
--   $$
--   This is the central min-max theorem of matching theory. Every maximum matching has a certificate of optimality in the form of a node set $A$, even when no node cover of the same size exists.
--
--   **Formalization Note** The two optima are stated as a single rational number $m$ that is the greatest size of a matching and the least value of the bound, so both are attained.
--
--   Differences from the source:
--   - reading: a matching is a set of edges such that no node is incident with more than one of them (p. 127) → IsMatching also requires that no edge of M is a loop; reason: the book's next sentences say M covers exactly 2|M| nodes and leaves |V| − 2|M| exposed, which fails for a loop
--   - encoding: |V|, |M|, |A| for finite sets → Nat.card V and Set.ncard, with binders [Finite V] [Finite E]; reason: these are the true cardinalities of finite sets
--   - encoding: ½(·) and (|V(C)| − 1)/2 on integers → the expression in ℚ after casting every cardinal; reason: no truncation; the value of the book's expression
--   - encoding: max{…} = min{…} → ∃ m : ℚ, IsGreatest {…} m ∧ IsLeast {…} m; reason: states attainment of both optima and their equality
--   - encoding: oc(H), the number of odd components of H; G\A → odd connected components of H.toSimple (distinct nodes adjacent iff some edge joins them); G\A on the node and edge subtypes outside A; reason: loops and parallel edges do not change which nodes are joined by a path, so the components are the book's
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 5.2, p. 131 (PDF p. 139)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_IsMatching
import Definitions.Def_CombOpt_TutteBerge_Multigraph_tutteBergeBound

namespace CombOpt.TutteBerge

/-- **Theorem 5.2 (Tutte–Berge Formula).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 5.2, p. 131 (PDF p. 139): "For a graph G = (V, E) we have
max{|M| : M a matching} = min{½(|V| − oc(G\A) + |A|) : A ⊆ V}."

The two optima are stated as one number `m`: `m` is the greatest size of a matching and the least
value of the bound, so both are attained and they are equal. -/
theorem tutte_berge_formula {V E : Type*} [Finite V] [Finite E] (G : Multigraph V E) :
    ∃ m : ℚ,
      IsGreatest {r : ℚ | ∃ M : Set E, G.IsMatching M ∧ r = (M.ncard : ℚ)} m ∧
      IsLeast {r : ℚ | ∃ A : Set V, r = G.tutteBergeBound A} m := by sorry

end CombOpt.TutteBerge
