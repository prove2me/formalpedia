-- Prove2me | Theorems.Thm_CLRS_DFS_ordered_correctness_and_explicit_running_time
-- name    : CLRS.DFS.ordered_correctness_and_explicit_running_time
-- status  : Proved
-- author  : @Chutong
-- created : 2026-10-14T21:36:13.685344+00:00
-- url     : https://prove2.me/theorems/6a8add2d-e73d-49d4-ba2d-dfd3aac5cda5
-- title:
--   Ordered DFS: reusable forest and an explicit linear event bound
-- statement:
--   For any represented finite graph and any allocated sequence whose first n entries permute the vertices, establish a terminating ordered DFS Call with the full forest, timestamp, white-path, root-priority, increasing finish-order, and dense tree-label contract. Its six output arrays and result object must be fresh, and all initial caller storage must be preserved. For the same call, prove $$T\le 4+6n+2m.$$ The bound holds for every root permutation, initial heap, and initial clock value, including the empty graph. This explicit open contract can be reused by the identity-order DFS wrapper and a later SCC proof.
-- source:
--   CLRS, Introduction to Algorithms, fourth edition (MIT Press, 2022), Chapter 20, §20.3. https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/ ; new arrays-of-arrays implementation compiled with Algo2Lean v0.1.4, https://www.algo2lean.com/versions/v0.1.4/ . Source filenames and full code are in the mission description.

import Definitions.Def_CLRS_DFS_Program

set_option autoImplicit false

open Algo2LeanGenerated CLRS.GraphTraversal CLRS.DFS

theorem CLRS.DFS.ordered_correctness_and_explicit_running_time
    (before : Heap) (graph : ObjectRef) (g : Graph) (inputOrder : SeqRef)
    (represented : GraphRep before graph g)
    (orderAllocated : inputOrder < before.nextRef)
    (orderValid : VertexOrder g (before.read inputOrder)) :
    ∃ (after : Heap) (result : ObjectRef),
      Algo.dfs.dfs_ordered.Call before (graph, inputOrder) after result ∧
      Post before after result g (before.read inputOrder) ∧
      work before after ≤ 4 + 6 * g.size + 2 * edgeCount g := by
  sorry
