-- Prove2me | Theorems.Thm_ConsistentSubmodular_Checkpoints_card_path_le
-- name    : ConsistentSubmodular.Checkpoints.card_path_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:41.229863+00:00
-- url     : https://prove2.me/theorems/c59b2ba3-825e-4db0-8781-28a7c3f6e224
-- title:
--   Intermediate cores of a transition are not larger than the endpoints
-- statement:
--   Let $C,A$ be finite sets of elements. For $r\in\mathbb N$ let $\mathrm{path}(C,A,r)$ be the core obtained from $C$ after $r$ operations of the transition from $C$ to $A$: the first $r$ elements of $C\setminus A$ are deleted and the first $r$ elements of $A\setminus C$ are inserted (in a fixed enumeration). Then for every $r$
--   $$\bigl|\mathrm{path}(C,A,r)\bigr|\;\le\;\max\bigl(|C|,\,|A|\bigr).$$
--
--   Every intermediate core of the checkpoint schedule therefore satisfies the cardinality budget whenever both endpoint cores do.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/CheckpointSchedule.lean#L81-L95 (`ConsistentSubmodular.Checkpoints.card_path_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointSchedule

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ}

theorem ConsistentSubmodular.Checkpoints.card_path_le (C A : Finset (Fin n)) (r : ℕ) :
    (path C A r).card ≤ max C.card A.card := by sorry
