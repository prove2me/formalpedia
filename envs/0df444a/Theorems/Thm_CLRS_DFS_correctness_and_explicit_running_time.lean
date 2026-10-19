-- Prove2me | Theorems.Thm_CLRS_DFS_correctness_and_explicit_running_time
-- name    : CLRS.DFS.correctness_and_explicit_running_time
-- status  : Proved
-- author  : @Chutong
-- created : 2026-10-14T21:36:25.882859+00:00
-- url     : https://prove2.me/theorems/e84f428d-d501-4e8b-8d7f-26da85c86ee7
-- title:
--   DFS: complete forest and an explicit linear event bound
-- statement:
--   For every represented finite directed graph, establish one terminating identity-order DFS Call with the complete forest and storage postconditions and $$T\le 7+8n+2m.$$ The cost includes creating identity order and the complete ordered DFS, including its recursive calls. Empty graphs, parallel arcs, self-loops, arbitrary heaps, and arbitrary initial counters are covered. This explicit supporting theorem is open.
-- source:
--   CLRS, Introduction to Algorithms, fourth edition (MIT Press, 2022), Chapter 20, §20.3. https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/ ; new arrays-of-arrays implementation compiled with Algo2Lean v0.1.4, https://www.algo2lean.com/versions/v0.1.4/ . Source filenames and full code are in the mission description.

import Definitions.Def_CLRS_DFS_Program

set_option autoImplicit false

open Algo2LeanGenerated CLRS.GraphTraversal CLRS.DFS

theorem CLRS.DFS.correctness_and_explicit_running_time
    (before : Heap) (graph : ObjectRef) (g : Graph)
    (represented : GraphRep before graph g) :
    ∃ (after : Heap) (result : ObjectRef),
      Algo.dfs.dfs.Call before graph after result ∧
      Post before after result g (fun i : Int => i) ∧
      work before after ≤ 7 + 8 * g.size + 2 * edgeCount g := by
  sorry
