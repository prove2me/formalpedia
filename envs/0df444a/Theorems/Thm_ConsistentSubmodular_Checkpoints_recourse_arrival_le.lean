-- Prove2me | Theorems.Thm_ConsistentSubmodular_Checkpoints_recourse_arrival_le
-- name    : ConsistentSubmodular.Checkpoints.recourse_arrival_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:55.251212+00:00
-- url     : https://prove2.me/theorems/574c07e4-6acd-4f65-8431-367290e98980
-- title:
--   One arrival changes a block's arrived part by at most one element
-- statement:
--   Let $B$ be a set of elements of $\{0,\dots,n-1\}$ and $t\in\mathbb N$, and let $X_t=\{e: e<t\}$ be the arrived prefix after $t$ arrivals. Then
--   $$\bigl|(B\cap X_{t+1})\,\triangle\,(B\cap X_t)\bigr|\;\le\;1.$$
--
--   One new arrival changes the arrived part of a block by at most one element. This bound on the per-arrival change is used when bounding the recourse of the checkpoint algorithm.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/CheckpointSchedule.lean#L124-L142 (`ConsistentSubmodular.Checkpoints.recourse_arrival_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {n : ℕ}

theorem ConsistentSubmodular.Checkpoints.recourse_arrival_le (B : Finset (Fin n)) (t : ℕ) :
    recourse (B ∩ arrivedPrefix n (t + 1)) (B ∩ arrivedPrefix n t) ≤ 1 := by sorry
