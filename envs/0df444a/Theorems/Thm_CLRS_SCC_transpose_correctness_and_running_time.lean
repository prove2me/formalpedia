-- Prove2me | Theorems.Thm_CLRS_SCC_transpose_correctness_and_running_time
-- name    : CLRS.SCC.transpose_correctness_and_running_time
-- status  : Proved
-- author  : @Chutong
-- created : 2026-10-14T21:38:40.413167+00:00
-- url     : https://prove2.me/theorems/b53453b0-4f75-4d76-a321-07f0cdd34ea0
-- title:
--   Graph transpose: correctness and uniform linear running time
-- statement:
--   For every represented graph, establish a terminating transpose Call returning a fresh graph object that represents the reversed adjacency occurrences with their multiplicities. Vertex count and total occurrence count are unchanged, and initial caller storage is preserved. One positive constant, uniform over graphs, heaps, and clocks, must bound the same call’s work by $$T\le C(1+n+m).$$ The empty graph is included. This reusable construction theorem is open.
-- source:
--   CLRS, Introduction to Algorithms, fourth edition (MIT Press, 2022), Chapter 20, §20.5. https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/ ; new arrays-of-arrays implementation compiled with Algo2Lean v0.1.4, https://www.algo2lean.com/versions/v0.1.4/ . Source filenames and full code are in the mission description.

import Definitions.Def_CLRS_SCC_Program

set_option autoImplicit false

open Algo2LeanGenerated CLRS.GraphTraversal CLRS.SCC

theorem CLRS.SCC.transpose_correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
      ∀ (before : Heap) (graph : ObjectRef) (g : Graph),
        GraphRep before graph g →
        ∃ after result,
          Algo.scc.transpose.Call before graph after result ∧
          TransposePost before after result g ∧
          work before after ≤ C * (1 + g.size + edgeCount g) := by
  sorry
