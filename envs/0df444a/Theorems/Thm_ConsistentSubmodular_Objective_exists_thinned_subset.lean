-- Prove2me | Theorems.Thm_ConsistentSubmodular_Objective_exists_thinned_subset
-- name    : ConsistentSubmodular.Objective.exists_thinned_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:35.973425+00:00
-- url     : https://prove2.me/theorems/e8c34bcc-ce8b-44ea-bd23-02513a9dfffc
-- title:
--   Thinning — a subset of prescribed size retains a proportional fraction of the value
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on $\{0,\dots,n-1\}$, let $A$ be a finite set and let $r$ be an integer with $r\le |A|$. Then there exists $B\subseteq A$ with $|B|=r$ such that
--   $$r\,f(A)\;\le\;|A|\,f(B).$$
--
--   Thus every set has a subset of any prescribed cardinality retaining at least the fraction $r/|A|$ of its value. This is the standard cardinality thinning bound, used to cut a set down to the budget while losing a controlled fraction of value.
--
--   **Formalization Note**: the baseline $f(\emptyset)$ is allowed to be positive; the inequality is stated for $f(A)$ and $f(B)$ directly, not for the gains over $f(\emptyset)$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/Thinning.lean#L56-L90 (`ConsistentSubmodular.Objective.exists_thinned_subset`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem ConsistentSubmodular.Objective.exists_thinned_subset (A : Finset (Fin n)) (r : ℕ) (hr : r ≤ A.card) :
    ∃ B ⊆ A, B.card = r ∧ (r : ℝ) * f.value A ≤ (A.card : ℝ) * f.value B := by sorry
