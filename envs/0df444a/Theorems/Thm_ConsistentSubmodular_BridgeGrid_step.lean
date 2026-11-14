-- Prove2me | Theorems.Thm_ConsistentSubmodular_BridgeGrid_step
-- name    : ConsistentSubmodular.BridgeGrid.step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:29.345327+00:00
-- url     : https://prove2.me/theorems/d8812be8-0432-4640-bf31-3ed710707236
-- title:
--   Consecutive grid points of the bridge are at $\ell_1$ distance at most $2/K$
-- statement:
--   For $K\ge 1$ and $0\le j\le K$ let $\pi_j=(1-\tfrac jK)\,\delta_0+\tfrac jK\,\delta_1$ be the $j$-th point of the uniform grid on the segment from the vertex $\delta_0$ to the vertex $\delta_1$ of the simplex on two candidates. Then for every $j<K$,
--   $$\|\pi_j-\pi_{j+1}\|_1\;=\;\sum_i|\pi_j(i)-\pi_{j+1}(i)|\;\le\;\frac 2K .$$
--
--   The grid path from $\delta_0$ to $\delta_1$ therefore moves in steps of $\ell_1$ length at most $2/K$, so each step has small recourse. This is the discretization of the bridge between the two cores.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/BridgeGrid.lean#L32-L45 (`ConsistentSubmodular.BridgeGrid.step`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_BridgeGrid

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.BridgeGrid
variable {n : ℕ}

theorem ConsistentSubmodular.BridgeGrid.step (K : ℕ) (hK : 0 < K) (j : Fin K) :
    typeL1 (point K j.castSucc) (point K j.succ) ≤ 2 / K := by sorry
