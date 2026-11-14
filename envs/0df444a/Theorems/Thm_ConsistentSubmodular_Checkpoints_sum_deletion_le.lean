-- Prove2me | Theorems.Thm_ConsistentSubmodular_Checkpoints_sum_deletion_le
-- name    : ConsistentSubmodular.Checkpoints.sum_deletion_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:13.534097+00:00
-- url     : https://prove2.me/theorems/daa29aca-1fdd-46d7-bab7-3411d8808318
-- title:
--   Deletion marginals telescope: $\sum_e\bigl(f(A)-f(A\setminus e)\bigr)\le f(A)-f(\emptyset)$
-- statement:
--   Let $f$ be a nonnegative monotone submodular function on subsets of $\{0,\dots,n-1\}$ and let $A$ be a finite set. Then
--   $$\sum_{e\in A}\Bigl(f(A)-f(A\setminus\{e\})\Bigr)\;\le\; f(A)-f(\emptyset).$$
--
--   The deletion marginals of $A$ add up to at most $f(A)-f(\emptyset)$. This is the telescoping step behind the thinning inequality (43) of the checkpoint reduction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/CheckpointWindow.lean#L60-L77 (`ConsistentSubmodular.Checkpoints.sum_deletion_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {n : ℕ}

theorem ConsistentSubmodular.Checkpoints.sum_deletion_le (f : Objective n) (A : Finset (Fin n)) :
    ∑ e ∈ A, (f.value A - f.value (A.erase e)) ≤ f.value A - f.value ∅ := by sorry
