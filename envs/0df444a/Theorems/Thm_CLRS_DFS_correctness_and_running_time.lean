-- Prove2me | Theorems.Thm_CLRS_DFS_correctness_and_running_time
-- name    : CLRS.DFS.correctness_and_running_time
-- status  : Proved
-- author  : @Chutong
-- created : 2026-10-14T21:36:40.305994+00:00
-- url     : https://prove2.me/theorems/db2f8c51-08d7-49d1-8f7a-1fa21757f6ab
-- title:
--   DFS: correctness and uniform linear running time
-- statement:
--   There is one positive natural constant C such that every heap representing a finite directed graph admits a terminating call to the displayed identity-order DFS with fresh outputs, preserved caller storage, the full forest/timestamp/white-path contract, and $$T\le C(1+n+m).$$ C is independent of all graph data, heaps, and initial clocks. The result lists vertices in increasing finish time and labels predecessor trees, not SCCs. Empty graphs are included. No algorithm proof is supplied.
-- source:
--   CLRS, Introduction to Algorithms, fourth edition (MIT Press, 2022), Chapter 20, §20.3. https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/ ; new arrays-of-arrays implementation compiled with Algo2Lean v0.1.4, https://www.algo2lean.com/versions/v0.1.4/ . Source filenames and full code are in the mission description.

import Definitions.Def_CLRS_DFS_Program

set_option autoImplicit false

open Algo2LeanGenerated CLRS.GraphTraversal CLRS.DFS

theorem CLRS.DFS.correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
      ∀ (before : Heap) (graph : ObjectRef) (g : Graph),
        GraphRep before graph g →
        ∃ (after : Heap) (result : ObjectRef),
          Algo.dfs.dfs.Call before graph after result ∧
          Post before after result g (fun i : Int => i) ∧
          work before after ≤ C * (1 + g.size + edgeCount g) := by
  sorry
