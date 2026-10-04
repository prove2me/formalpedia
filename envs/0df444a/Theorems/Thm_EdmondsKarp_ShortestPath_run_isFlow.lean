-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_run_isFlow
-- name    : EdmondsKarp.ShortestPath.run_isFlow
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T19:28:55.874033+00:00
-- url     : https://prove2.me/theorems/64d98bfa-0b76-4609-b410-914998859337
-- title:
--   Every state of a shortest augmenting-path run is feasible
-- statement:
--   In a finite shortest augmenting-path run, the flow at every index from zero through the terminal index is feasible.
-- source:
--   Edmonds and Karp (1972), Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, §1.1 pp. 249–250 and §1.2 p. 251. DOI: 10.1145/321694.321699.

import Definitions.Def_EdmondsKarp_ShortestPath_Run
open EdmondsKarp.ShortestPath

theorem EdmondsKarp.ShortestPath.run_isFlow {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (K : ℕ) (f : ℕ → V → V → ℝ) (P : ℕ → List V) (hrun : IsShortestRun N K f P)
    (k : ℕ) (hk : k ≤ K) : IsFlow N (f k) := by sorry
