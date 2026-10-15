-- Prove2me | Theorems.Thm_CLRS_BFS_correctness_and_running_time
-- name    : CLRS.BFS.correctness_and_running_time
-- status  : Open
-- author  : @Chutong
-- created : 2026-10-14T21:21:38.164664+00:00
-- url     : https://prove2.me/theorems/af3b6ccc-1872-445a-a77b-d12936a58fe3
-- title:
--   BFS: correctness and uniform linear running time
-- statement:
--   There is one positive natural constant C, independent of the graph, source, initial heap, and counters, such that every represented finite graph with a valid source has a terminating BFS call returning exact shortest distances, correct predecessors, fresh outputs, and preserved caller storage, with $$T\le C(1+n+m).$$ The source must be in 0,…,n−1, excluding the empty graph. T counts the displayed graph_work events, not bit complexity or elapsed time. The algorithm proof and this uniform bound remain contributor tasks.
-- source:
--   CLRS, Introduction to Algorithms, fourth edition (MIT Press, 2022), Chapter 20, §20.2. https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/ ; new arrays-of-arrays implementation compiled with Algo2Lean v0.1.4, https://www.algo2lean.com/versions/v0.1.4/ . Source filenames and full code are in the mission description.

import Definitions.Def_CLRS_BFS_Program

set_option autoImplicit false

open Algo2LeanGenerated CLRS.GraphTraversal CLRS.BFS

theorem CLRS.BFS.correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
      ∀ (before : Heap) (graph : ObjectRef) (g : Graph) (source : Int),
        GraphRep before graph g → Vertex g source →
        ∃ after result,
          Algo.bfs.bfs.Call before (graph, source) after result ∧
          Post before after result g source ∧
          work before after ≤ C * (1 + g.size + edgeCount g) := by
  sorry
