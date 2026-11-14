-- Prove2me | Theorems.Thm_ConsistentSubmodular_IntervalSelection_value_union_le
-- name    : ConsistentSubmodular.IntervalSelection.value_union_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:47.995026+00:00
-- url     : https://prove2.me/theorems/308ba846-cbe3-43a0-aa72-d67fa22ac09a
-- title:
--   Elements worth no more than $\emptyset$ add nothing
-- statement:
--   Let $f$ be a nonnegative monotone submodular function on subsets of $\{0,\dots,n-1\}$ and let $A,X$ be sets such that $f(\{e\})\le f(\emptyset)$ for every $e\in A$. Then
--   $$f(A\cup X)\le f(X).$$
--
--   This handles the degenerate case in which some candidate elements have no marginal value, and is used in the treatment of the case $f(O_0)=0$ in the proof of Lemma 2.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/IntervalSelection.lean#L59-L73 (`ConsistentSubmodular.IntervalSelection.value_union_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {n : ℕ} (f : Objective n)

theorem ConsistentSubmodular.IntervalSelection.value_union_le (A X : Finset (Fin n)) (h : ∀ e ∈ A, f.value {e} ≤ f.value ∅) :
    f.value (A ∪ X) ≤ f.value X := by sorry
