-- Prove2me | Theorems.Thm_ConsistentSubmodular_Objective_optimum_thinning
-- name    : ConsistentSubmodular.Objective.optimum_thinning
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:45.804277+00:00
-- url     : https://prove2.me/theorems/cd765ae4-3260-4935-9601-944b9b0d3f63
-- title:
--   Cardinality thinning inequality for exact optima
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on $\{0,\dots,n-1\}$, let $N$ be a finite set, and let $r\le k$ be natural numbers. Write
--   $$\mathrm{OPT}_j=\max\{f(B):\ B\subseteq N,\ |B|\le j\}$$
--   for the exact optimum of cardinality at most $j$ over $N$ with empty buffer. Then
--   $$r\cdot \mathrm{OPT}_k\;\le\;k\cdot \mathrm{OPT}_r .$$
--
--   Equivalently, $\mathrm{OPT}_r/r$ is nonincreasing in $r$: the optimum with budget $r$ is at least an $r/k$ fraction of the optimum with budget $k$. This is the standard thinning inequality, used to compare optima for different budgets.
--
--   **Formalization Note**: $\mathrm{OPT}_j$ is `bufferedOptimum N ∅ j`, the value of a chosen exact maximizer.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/Thinning.lean#L92-L111 (`ConsistentSubmodular.Objective.optimum_thinning`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Model

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem ConsistentSubmodular.Objective.optimum_thinning (N : Finset (Fin n)) {r k : ℕ} (hrk : r ≤ k) :
    (r : ℝ) * f.bufferedOptimum N ∅ k ≤
      (k : ℝ) * f.bufferedOptimum N ∅ r := by sorry
