-- Prove2me | Theorems.Thm_ConsistentSubmodular_Objective_sum_removal_marginals_le
-- name    : ConsistentSubmodular.Objective.sum_removal_marginals_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:38.337975+00:00
-- url     : https://prove2.me/theorems/fb6186c6-2cc5-4b2a-b0f1-f08301dac56b
-- title:
--   Removal marginals sum to at most the residual value
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on $\{0,\dots,n-1\}$ and let $A$ be a finite subset. Then
--   $$\sum_{e\in A}\bigl(f(A)-f(A\setminus\{e\})\bigr)\;\le\;f(A)-f(\emptyset).$$
--
--   The sum of all removal marginals of $A$ is bounded by the residual total value of $A$ above the empty set. This follows from submodularity, and it is used in the thinning arguments to show that a set has few elements with large removal marginal.
--
--   **Formalization Note**: $f(\emptyset)$ need not be zero, so it appears explicitly in the bound.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/Thinning.lean#L23-L36 (`ConsistentSubmodular.Objective.sum_removal_marginals_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem ConsistentSubmodular.Objective.sum_removal_marginals_le (A : Finset (Fin n)) :
    (∑ e ∈ A, (f.value A - f.value (A.erase e))) ≤ f.value A - f.value ∅ := by sorry
