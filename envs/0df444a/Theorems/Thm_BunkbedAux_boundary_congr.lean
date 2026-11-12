-- Prove2me | Theorems.Thm_BunkbedAux_boundary_congr
-- name    : BunkbedAux.boundary_congr
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T03:58:12.48656+00:00
-- url     : https://prove2.me/theorems/2521a542-dfb8-4744-891b-35969f4c1918
-- title:
--   Connectivity depends only on the boundary partitions
-- statement:
--   When a graph is assembled from pieces that meet only along a distinguished set of *boundary* vertices, connectivity between boundary vertices cannot depend on the internal structure of the pieces beyond which boundary vertices each piece joins together. This theorem makes that precise.
--
--   Let $S_i$ and $S'_i$, for $i$ in a finite index type, be two families of edge sets, and let $B$ be a set of boundary vertices. Assume:
--
--   - corresponding parts induce the **same reachability relation on $B$**: for all $i$ and all $p, q \in B$, $p$ and $q$ are connected using only the edges of $S_i$ precisely when they are connected using only those of $S'_i$;
--   - in each family, every vertex outside $B$ is touched by **at most one** part.
--
--   Then for boundary vertices $x, y \in B$, $x$ and $y$ are connected in $\bigcup_i S_i$ precisely when they are connected in $\bigcup_i S'_i$.
--
--   The reason is that a walk in the union can only pass from one part to another at a vertex shared by both, and by the second hypothesis such a vertex must lie in $B$. So the walk decomposes into segments, each staying within a single part and running between boundary vertices; the first hypothesis transfers each segment to the other family, and concatenating the transferred segments reconnects $x$ to $y$.
--
--   **Mathematical role.** This is the second of the two ingredients needed to analyse a graph built by substituting a gadget for each hyperedge of a hypergraph. Its effect is to collapse the enormous configuration space of the substituted graph: the only thing a gadget copy's internal configuration contributes is the partition it induces on its three attachment vertices. Combined with independence across the edge-disjoint copies, this is what identifies percolation on the substituted graph with a Wierman--Ziff model on the hypergraph, in which each hyperedge independently takes one of five states.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 4 (pp. 6-7), where a gadget graph is substituted for each hyperedge.

import Definitions.Def_BunkbedPercolation
open Bunkbed Finset SimpleGraph

namespace BunkbedAux

/-- **Connectivity depends only on the boundary partitions.** Suppose two families of edge sets
induce the same reachability relation on a boundary set `B`, and in each family every non-boundary
vertex is touched by only one part. Then the two unions have the same reachability between
boundary vertices. -/
theorem boundary_congr {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S S' : ι → Finset (Sym2 V)) (B : Finset V)
    (hsame : ∀ i, ∀ p ∈ B, ∀ q ∈ B,
      ((ofEdges (S i)).Reachable p q ↔ (ofEdges (S' i)).Reachable p q))
    (hsupp : ∀ i, ∀ e ∈ S i, ∀ v ∈ e, v ∉ B → ∀ j, j ≠ i → ∀ f ∈ S j, v ∉ f)
    (hsupp' : ∀ i, ∀ e ∈ S' i, ∀ v ∈ e, v ∉ B → ∀ j, j ≠ i → ∀ f ∈ S' j, v ∉ f)
    (x y : V) (hx : x ∈ B) (hy : y ∈ B) :
    ((ofEdges (Finset.univ.biUnion S)).Reachable x y
      ↔ (ofEdges (Finset.univ.biUnion S')).Reachable x y) := by
  sorry

end BunkbedAux
