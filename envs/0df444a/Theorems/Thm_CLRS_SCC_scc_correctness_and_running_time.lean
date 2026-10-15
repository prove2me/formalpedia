-- Prove2me | Theorems.Thm_CLRS_SCC_scc_correctness_and_running_time
-- name    : CLRS.SCC.scc_correctness_and_running_time
-- status  : Open
-- author  : @Chutong
-- created : 2026-10-14T21:39:07.531341+00:00
-- url     : https://prove2.me/theorems/6c9ab06c-8bf2-4a19-a9d8-be31f584b1fd
-- title:
--   SCC: correctness and uniform linear running time
-- statement:
--   There is one positive natural constant C, uniform over all graph data, input heaps, and initial counters, such that the displayed SCC program terminates and returns a fresh exact partition into strongly connected components with preserved caller storage and $$T\le C(1+n+m).$$ Equal labels are equivalent to mutual reachability in the original graph; labels are contiguous and all used, but their numeric values are not canonical. Empty and disconnected graphs, parallel arcs, and self-loops are included. The bound covers both DFS passes and graph preparation. This is an open task; no correctness or runtime proof is supplied.
-- source:
--   CLRS, Introduction to Algorithms, fourth edition (MIT Press, 2022), Chapter 20, §20.5. https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/ ; new arrays-of-arrays implementation compiled with Algo2Lean v0.1.4, https://www.algo2lean.com/versions/v0.1.4/ . Source filenames and full code are in the mission description.

import Definitions.Def_CLRS_SCC_Program

set_option autoImplicit false

open Algo2LeanGenerated CLRS.GraphTraversal CLRS.SCC

theorem CLRS.SCC.scc_correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
      ∀ (before : Heap) (graph : ObjectRef) (g : Graph),
        GraphRep before graph g →
        ∃ after result,
          Algo.scc.scc.Call before graph after result ∧
          Post before after result g ∧
          work before after ≤ C * (1 + g.size + edgeCount g) := by
  sorry
