-- Prove2me | Theorems.Thm_CLRS_DFS_ordered_local_certificate
-- name    : CLRS.DFS.ordered_local_certificate
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T03:17:45.248539+00:00
-- url     : https://prove2.me/theorems/8135efa2-551c-47b2-9e46-b1120b5b6dd6
-- title:
--   Ordered DFS execution with local timestamp and label invariants
-- statement:
--   Let $G$ be a represented finite directed multigraph, with $n$ vertices and $m$ adjacency occurrences, in an arbitrary initial heap. Let an allocated input sequence have a vertex permutation in its first $n$ entries. The generated ordered recursive DFS has a completed call, valid under every suspended caller stack, returning a fresh result object and six distinct fresh arrays. All initial sequences, objects, and collections are preserved, allocation counters and the work clock do not decrease, and other clocks are unchanged. The completed call satisfies
--   $$T\le4+6n+2m.$$
--
--   Its returned colors are black, its event clock and finish count are $2n$ and $n$, and its tree count is at most $n$. Its parent, discovery, finish, increasing-finish order, and tree-label arrays satisfy the local certificate: distinct valid event times with nested or disjoint intervals; parent edges and strictly containing parent intervals; the nearest-enclosing-parent condition; discovery of every edge target before its source finishes; root priority; increasing permutation of finish times; dense bounded labels inherited across parent links; and label order agreeing with discovery order at roots.
--
--   The certificate contains no parent-path or white-path equivalence and no common-root characterization of equal labels. These global properties can be established separately from the local invariants. The empty graph, duplicated adjacency occurrences, self-loops, aliasing among input rows, and arbitrary initial clocks are included.
-- source:
--   CLRS, Introduction to Algorithms, fourth edition, Section 20.3, DFS and DFS-VISIT, Theorems 20.7 and 20.9; local operational sublemma for the existing ordered DFS milestone. Supporting exposition: Jessica Su, Stanford CS 161 Lecture 10, Sections 2.1–2.4, PDF pages 5–9, https://web.stanford.edu/class/archive/cs/cs161/cs161.1168/lecture10-draft.pdf . Generated transitions are Definitions.Def_CLRS_DFS_Program on Prove2Me.

import Definitions.Def_CLRS_DFS_LocalCertificate

set_option autoImplicit false
open Algo2LeanGenerated CLRS.GraphTraversal CLRS.DFS

theorem CLRS.DFS.ordered_local_certificate
    (before : Heap) (graph : ObjectRef) (g : Graph) (inputOrder : SeqRef)
    (represented : GraphRep before graph g)
    (orderAllocated : inputOrder < before.nextRef)
    (orderValid : VertexOrder g (before.read inputOrder)) :
    ∃ (after : Heap) (result : ObjectRef),
      Algo.dfs.dfs_ordered.Call before (graph, inputOrder) after result ∧
      LocalPost before after result g (before.read inputOrder) ∧
      work before after ≤ 4 + 6 * g.size + 2 * edgeCount g := by sorry
