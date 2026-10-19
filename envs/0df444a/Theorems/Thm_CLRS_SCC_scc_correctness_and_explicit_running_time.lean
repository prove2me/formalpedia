-- Prove2me | Theorems.Thm_CLRS_SCC_scc_correctness_and_explicit_running_time
-- name    : CLRS.SCC.scc_correctness_and_explicit_running_time
-- status  : Proved
-- author  : @Chutong
-- created : 2026-10-14T21:38:52.512973+00:00
-- url     : https://prove2.me/theorems/6bdb619a-fbbe-4e40-a86a-c303ca6786cf
-- title:
--   SCC: exact component partition and an explicit event bound
-- statement:
--   For every represented graph, establish a terminating call to the displayed two-pass SCC program. Its fresh labels must agree exactly for mutually reachable vertices, range over 0,…,k−1 with every label used, satisfy k≤n and k=0 exactly when n=0, and preserve caller storage. For the same call, prove $$T\le 20+21n+6m,$$ including both DFS passes, transposition, and linear reversal of finish order. The result is an open theorem with no assumed-correct DFS hypothesis.
-- source:
--   CLRS, Introduction to Algorithms, fourth edition (MIT Press, 2022), Chapter 20, §20.5. https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/ ; new arrays-of-arrays implementation compiled with Algo2Lean v0.1.4, https://www.algo2lean.com/versions/v0.1.4/ . Source filenames and full code are in the mission description.

import Definitions.Def_CLRS_SCC_Program

set_option autoImplicit false

open Algo2LeanGenerated CLRS.GraphTraversal CLRS.SCC

theorem CLRS.SCC.scc_correctness_and_explicit_running_time
    (before : Heap) (graph : ObjectRef) (g : Graph)
    (represented : GraphRep before graph g) :
    ∃ after result,
      Algo.scc.scc.Call before graph after result ∧
      Post before after result g ∧
      work before after ≤ 20 + 21 * g.size + 6 * edgeCount g := by
  sorry
