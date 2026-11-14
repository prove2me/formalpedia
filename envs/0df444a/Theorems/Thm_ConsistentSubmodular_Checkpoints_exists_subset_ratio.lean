-- Prove2me | Theorems.Thm_ConsistentSubmodular_Checkpoints_exists_subset_ratio
-- name    : ConsistentSubmodular.Checkpoints.exists_subset_ratio
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:27.965537+00:00
-- url     : https://prove2.me/theorems/c0298e17-e0a3-48eb-a615-1e89c36d9689
-- title:
--   Thinning inequality (43) with a general size
-- statement:
--   Let $f$ be a nonnegative monotone submodular function on subsets of $\{0,\dots,n-1\}$. For every $m\in\mathbb N$, every set $A$ with $|A|=m$, and every $r\le m$, there is a subset $T\subseteq A$ with $|T|=r$ and
--   $$r\,f(A)\;\le\; m\,f(T).$$
--
--   Such a $T$ is obtained by repeated deletion of a cheap element. This is the thinning inequality (43) in general form, used in the checkpoint reduction to keep a fraction of the value while reducing the size of a core.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/CheckpointWindow.lean#L91-L139 (`ConsistentSubmodular.Checkpoints.exists_subset_ratio`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {n : ℕ}

theorem ConsistentSubmodular.Checkpoints.exists_subset_ratio (f : Objective n) :
    ∀ (m : ℕ) (A : Finset (Fin n)), A.card = m → ∀ r ≤ m,
      ∃ T ⊆ A, T.card = r ∧ (r : ℝ) * f.value A ≤ m * f.value T := by sorry
