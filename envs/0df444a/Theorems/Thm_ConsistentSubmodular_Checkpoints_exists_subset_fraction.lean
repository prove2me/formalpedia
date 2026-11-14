-- Prove2me | Theorems.Thm_ConsistentSubmodular_Checkpoints_exists_subset_fraction
-- name    : ConsistentSubmodular.Checkpoints.exists_subset_fraction
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:24.719891+00:00
-- url     : https://prove2.me/theorems/9c2cca4e-271c-435a-b547-8aac913a68d8
-- title:
--   Fractional subsets: $f(\mathrm{OPT}^{(\kappa)})\ge(\kappa/k)\,f(A)$
-- statement:
--   Let $f$ be a nonnegative monotone submodular function on subsets of $\{0,\dots,n-1\}$, let $k>0$ and $\kappa\le k$ be natural numbers, and let $A$ be a set with $|A|\le k$. Then there is $T\subseteq A$ with $|T|\le\kappa$ and
--   $$\frac{\kappa}{k}\,f(A)\;\le\; f(T).$$
--
--   Every set of at most $k$ elements has a subset of at most $\kappa\le k$ elements keeping a $\kappa/k$ fraction of its value. This is used in the checkpoint reduction to relate the optimum of a core of size $\kappa$ to the optimum under budget $k$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/CheckpointWindow.lean#L141-L158 (`ConsistentSubmodular.Checkpoints.exists_subset_fraction`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {n : ℕ}

theorem ConsistentSubmodular.Checkpoints.exists_subset_fraction (f : Objective n) {A : Finset (Fin n)} {κ k : ℕ}
    (hA : A.card ≤ k) (hκ : κ ≤ k) (hk : 0 < k) :
    ∃ T ⊆ A, T.card ≤ κ ∧ (κ : ℝ) / k * f.value A ≤ f.value T := by sorry
