-- Prove2me | Theorems.Thm_BasicPackArb_Main_Supplement_theorem_1_5
-- name    : BasicPackArb.Main.Supplement.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:01:25.186808+00:00
-- url     : https://prove2.me/theorems/369ad9a6-dec2-479c-a397-aeb8ae834524
-- title:
--   Theorem 1.5 — basic rooted-tree decompositions covering every edge
-- statement:
--   Let $G=(V,E)$ be a finite graph with placement $\pi:S\to V$, and let $M$ be a matroid on $S$ of rank $k=r_M(S)$. Write $V(F)$ for the vertices incident to $F$ and $S_X=\pi^{-1}(X)$. There is an $M$-basic rooted-tree packing whose edge union is all of $E$ if and only if all three conditions hold:
--
--   $$\pi\text{ is }M\text{-independent},\qquad |E|+|S|=k|V|,$$
--   $$|F|+|S_{V(F)}|\le k|V(F)|-k+r_M(S_{V(F)})\qquad(\varnothing\ne F\subseteq E).$$
--
--   Every nonempty edge subset is tested, and $V(F)$ excludes unrelated isolated vertices. The left side requires a decomposition of every edge, in addition to the basic packing conditions. This is the edge-covering companion attributed to Katoh and Tanigawa and proved in this paper.
--
--   Differences from the source:
--   - encoding: finite graphs, root sets and matroids on S → finite vertex/root carriers, finite edge sets with edge identities, and M.E = Set.univ; reason: these presentations include every source instance, preserve parallel edges and repeated roots, and express that the ground set is exactly S
--   - encoding: rank differences and partition counts → finite ranks converted from M.eRk and additive inequalities over integers; reason: finite ranks are ordinary natural numbers and integer rearrangement avoids truncated subtraction without changing any case
--   - encoding: connected cycle-free rooted subgraphs → root-containing vertex and edge sets with root reachability and the referenced multigraph edge-deletion acyclicity predicate; reason: this is exactly a connected acyclic multigraph, including a single-vertex tree; no spanning requirement is imposed
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 3, Theorem 1.5

import Definitions.Def_BasicPackArb_Main_Supplement_TreePacking

set_option autoImplicit false

namespace BasicPackArb.Main.Supplement

/-- Theorem 1.5, p. 3: edge-covering decomposition and every nonempty edge-set inequality. -/
theorem theorem_1_5 {V E S : Type} [Fintype V] [Fintype S]
    [DecidableEq V] [DecidableEq E] (G : Graph V E) (π : S → V)
    (M : Matroid S) (hground : M.E = Set.univ) :
    (∃ T : S → RootedTree G, IsTreePacking G π M T ∧ treeUnion T = G.edges) ↔
      MIndependent π M ∧
      (G.edges.card : ℤ) + Fintype.card S = (rank M Set.univ : ℤ) * Fintype.card V ∧
      ∀ F : Finset E, F ⊆ G.edges → F.Nonempty →
        (F.card : ℤ) + (roots π (G.incident F)).card + (rank M Set.univ : ℤ) ≤
          (rank M Set.univ : ℤ) * (G.incident F).card +
            (rank M (π ⁻¹' (G.incident F : Set V)) : ℤ) := by sorry

end BasicPackArb.Main.Supplement
