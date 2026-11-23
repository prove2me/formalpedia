-- Prove2me | Theorems.Thm_BasicPackArb_Main_Supplement_theorem_1_3
-- name    : BasicPackArb.Main.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:00:56.601422+00:00
-- url     : https://prove2.me/theorems/bd086c3b-15f1-4d34-89ae-0ec2d915d386
-- title:
--   Theorem 1.3 — basic rooted-tree packings
-- statement:
--   Let $G=(V,E)$ be a finite graph, $\pi:S\to V$ a placement of a finite root set, and $M$ a matroid on $S$. Then
--
--   $$\exists\ M\text{-basic packing of rooted trees in }(G,S,\pi)\quad\Longleftrightarrow\quad\pi\text{ is }M\text{-independent and }(G,S,\pi)\text{ is }M\text{-partition-connected}.$$
--
--   The family has one tree rooted at $\pi(s)$ for every $s\in S$, its trees are edge-disjoint, and the roots of the trees containing any vertex form an $M$-base. Independence means each fibre $S_v$ is independent. The partition condition is the full inequality for every nonempty-block partition. The trees may be singletons and need not span the graph. This is the undirected companion of the published directed goal.
--
--   Differences from the source:
--   - encoding: finite graphs, root sets and matroids on S → finite vertex/root carriers, finite edge sets with edge identities, and M.E = Set.univ; reason: these presentations include every source instance, preserve parallel edges and repeated roots, and express that the ground set is exactly S
--   - encoding: rank differences and partition counts → finite ranks converted from M.eRk and additive inequalities over integers; reason: finite ranks are ordinary natural numbers and integer rearrangement avoids truncated subtraction without changing any case
--   - encoding: connected cycle-free rooted subgraphs → root-containing vertex and edge sets with root reachability and the referenced multigraph edge-deletion acyclicity predicate; reason: this is exactly a connected acyclic multigraph, including a single-vertex tree; no spanning requirement is imposed
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 2, Theorem 1.3

import Definitions.Def_BasicPackArb_Main_Supplement_TreePacking

set_option autoImplicit false

namespace BasicPackArb.Main.Supplement

/-- Theorem 1.3, p. 2. Trees may be singletons and need not span V. -/
theorem theorem_1_3 {V E S : Type} [Fintype V] [Fintype S]
    [DecidableEq V] [DecidableEq E] (G : Graph V E) (π : S → V)
    (M : Matroid S) (hground : M.E = Set.univ) :
    (∃ T : S → RootedTree G, IsTreePacking G π M T) ↔
      MIndependent π M ∧ MPartitionConnected G π M := by sorry

end BasicPackArb.Main.Supplement
