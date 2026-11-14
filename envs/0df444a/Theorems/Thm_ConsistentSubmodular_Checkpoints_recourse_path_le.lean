-- Prove2me | Theorems.Thm_ConsistentSubmodular_Checkpoints_recourse_path_le
-- name    : ConsistentSubmodular.Checkpoints.recourse_path_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:20.029998+00:00
-- url     : https://prove2.me/theorems/c2896b14-e626-43ae-9bce-f612521e19ac
-- title:
--   Recourse of the transition path
-- statement:
--   Let $C,A$ be finite sets and $r\le r'$ natural numbers. With $\mathrm{path}(C,A,r)$ the core after $r$ operations of the transition from $C$ to $A$ (deleting the first $r$ elements of $C\setminus A$ and inserting the first $r$ elements of $A\setminus C$), the symmetric difference satisfies
--   $$\bigl|\mathrm{path}(C,A,r')\,\triangle\,\mathrm{path}(C,A,r)\bigr|\;\le\;2\,(r'-r).$$
--
--   That is, operations $r+1,\dots,r'$ change at most two elements each (one deletion and one insertion). This bounds the recourse of the checkpoint schedule.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/CheckpointSchedule.lean#L97-L113 (`ConsistentSubmodular.Checkpoints.recourse_path_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointSchedule

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ}

theorem ConsistentSubmodular.Checkpoints.recourse_path_le (C A : Finset (Fin n)) {r r' : ℕ} (h : r ≤ r') :
    recourse (path C A r') (path C A r) ≤ 2 * (r' - r) := by sorry
