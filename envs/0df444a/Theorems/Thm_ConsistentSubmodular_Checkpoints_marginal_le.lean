-- Prove2me | Theorems.Thm_ConsistentSubmodular_Checkpoints_marginal_le
-- name    : ConsistentSubmodular.Checkpoints.marginal_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:20.550059+00:00
-- url     : https://prove2.me/theorems/2c2c08a9-9bc9-46e2-8ef1-c239078a12aa
-- title:
--   Diminishing returns for marginal gains
-- statement:
--   Let $f$ be a nonnegative monotone submodular function on subsets of $\{0,\dots,n-1\}$, let $Y\subseteq X$ be sets and $e$ an element. Then
--   $$f(X\cup\{e\})-f(X)\;\le\; f(Y\cup\{e\})-f(Y).$$
--
--   Adding $e$ to a larger set gains less. This standard form of submodularity is used in the thinning arguments of the checkpoint reduction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/CheckpointWindow.lean#L30-L58 (`ConsistentSubmodular.Checkpoints.marginal_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {n : ℕ}

theorem ConsistentSubmodular.Checkpoints.marginal_le (f : Objective n) {X Y : Finset (Fin n)} (hYX : Y ⊆ X) (e : Fin n) :
    f.value (insert e X) - f.value X ≤ f.value (insert e Y) - f.value Y := by sorry
