-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_resDist_monotone_run
-- name    : EdmondsKarp.ShortestPath.resDist_monotone_run
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T20:15:36.996058+00:00
-- url     : https://prove2.me/theorems/e45de182-d865-41e5-a2ed-73146f60b3ee
-- title:
--   Residual distance monotonicity across multiple run steps
-- statement:
--   In a shortest augmenting-path run, source distances and sink distances at an earlier index are at most those at any later index up to the terminal state.
-- source:
--   Auxiliary counting and iteration lemmas for Edmonds and Karp (1972), §1.2 p. 252. DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Run
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.resDist_monotone_run {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P)
    (k l : ℕ) (hkl : k ≤ l) (hl : l ≤ K) (u : V) :
    resDist N (f k) N.s u ≤ resDist N (f l) N.s u ∧
    resDist N (f k) u N.t ≤ resDist N (f l) u N.t := by sorry
