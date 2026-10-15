-- Prove2me | Theorems.Thm_CLRS_BFS_correctness_and_explicit_running_time
-- name    : CLRS.BFS.correctness_and_explicit_running_time
-- status  : Open
-- author  : @Chutong
-- created : 2026-10-14T21:21:22.807686+00:00
-- url     : https://prove2.me/theorems/da64d58f-92ab-4230-8bb9-ad3e21eedc75
-- title:
--   BFS: shortest paths and an explicit linear event bound
-- statement:
--   For every heap representing the input graph and every valid source, establish one terminating BFS Call with the complete shortest-path, predecessor, fresh-result, and caller-preservation postcondition. For the same call, prove $$T\le 6n+2m+5.$$ Here T is the increment of graph_work and m counts adjacency occurrences. The initial clock values are arbitrary. This stronger numerical bound is an open supporting task.
-- source:
--   CLRS, Introduction to Algorithms, fourth edition (MIT Press, 2022), Chapter 20, §20.2. https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/ ; new arrays-of-arrays implementation compiled with Algo2Lean v0.1.4, https://www.algo2lean.com/versions/v0.1.4/ . Source filenames and full code are in the mission description.

import Definitions.Def_CLRS_BFS_Program

set_option autoImplicit false

open Algo2LeanGenerated CLRS.GraphTraversal CLRS.BFS

theorem CLRS.BFS.correctness_and_explicit_running_time
    (before : Heap) (graph : ObjectRef) (g : Graph) (source : Int)
    (represented : GraphRep before graph g) (sourceValid : Vertex g source) :
    ∃ after result,
      Algo.bfs.bfs.Call before (graph, source) after result ∧
      Post before after result g source ∧
      work before after ≤ 6 * g.size + 2 * edgeCount g + 5 := by
  sorry
