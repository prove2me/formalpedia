-- Prove2me | Theorems.Thm_CombOpt_TutteBerge_theorem_5_1
-- name    : CombOpt.TutteBerge.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:29.94098+00:00
-- url     : https://prove2.me/theorems/f917734e-3904-4d8e-9a66-59a8571d9a1d
-- title:
--   Theorem 5.1 — Augmenting Path Theorem of Matchings (corrected: augmenting paths are simple)
-- statement:
--   Let $M$ be a matching of a finite graph $G$. Then $M$ is a maximum matching if and only if there is no $M$-augmenting path.
--
--   This is Berge's characterization of maximum matchings, the optimality criterion behind augmenting-path algorithms.
--
--   **Formalization Note** The statement is on multigraphs. The simple-graph form is Proved on the platform as `BergeMatching.Core.theorem_1`, and is not imported because its graph type is different.
--
--   Differences from the source:
--   - correction: an M-augmenting path is an M-alternating path with distinct M-exposed end nodes, and a path may repeat nodes (pp. 10, 128) → Path.IsAugmenting also requires the path to be simple; reason: the printed statement is false for non-simple paths. Take nodes r, s, a, b, c, d, edges ra, sa, ab, bc, cd, db and M = {ab, cd}. The sequence r a b c d b a s is M-alternating with distinct M-exposed ends, while M is maximum: A = {a} gives oc(G\A) = 3, so ν(G) ≤ ½(6 − 3 + 1) = 2 = |M|. The book's proof uses M △ E(P) and paths of a node-disjoint decomposition, so it means simple paths
--   - reading: a matching is a set of edges such that no node is incident with more than one of them (p. 127) → IsMatching also requires that no edge of M is a loop; reason: the book's next sentences say M covers exactly 2|M| nodes and leaves |V| − 2|M| exposed, which fails for a loop
--   - encoding: |V|, |M|, |A| for finite sets → Nat.card V and Set.ncard, with binders [Finite V] [Finite E]; reason: these are the true cardinalities of finite sets
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 5.1, p. 129 (PDF p. 137)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph
import Definitions.Def_CombOpt_TutteBerge_Multigraph_IsMatching
import Definitions.Def_CombOpt_TutteBerge_Multigraph_IsMaximumMatching
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path
import Definitions.Def_CombOpt_TutteBerge_Multigraph_Path_IsAugmenting

namespace CombOpt.TutteBerge

/-- **Theorem 5.1 (Augmenting Path Theorem of Matchings).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 5.1, p. 129 (PDF p. 137): "A matching M in a graph G = (V, E) is maximum if and only
if there is no M-augmenting path."

**Formalization Note.** Augmenting paths are simple (`Path.IsAugmenting`); with repeated nodes
allowed the statement is false. -/
theorem theorem_5_1 {V E : Type*} [Finite V] [Finite E] (G : Multigraph V E) (M : Set E)
    (hM : G.IsMatching M) :
    G.IsMaximumMatching M ↔ ¬ ∃ (u w : V) (P : G.Path u w), P.IsAugmenting M := by sorry

end CombOpt.TutteBerge
