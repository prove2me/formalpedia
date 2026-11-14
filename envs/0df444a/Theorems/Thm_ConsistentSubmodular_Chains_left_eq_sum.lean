-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_left_eq_sum
-- name    : ConsistentSubmodular.Chains.left_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:39.127203+00:00
-- url     : https://prove2.me/theorems/18e55710-e17f-4c23-b700-42956cec3744
-- title:
--   Left endpoints of consecutive intervals are partial sums of lengths
-- statement:
--   Let $I$ be a nonincreasing consecutive interval instance with intervals $[\ell_i,r_i]$ for $i=0,\dots,N$, and lengths $d_i=r_i-\ell_i$. Then for every $j\in\{0,\dots,N\}$
--   $$\ell_j\;=\;\sum_{i<j}d_i,$$
--   where the sum runs over indices $i\in\{0,\dots,N\}$ with $i<j$ (the empty sum for $j=0$ is $0$).
--
--   This holds because the intervals are consecutive and start at $\ell_0=0$. It is used to express the quantities $B=\mathbb E[\ell_j]$ and $\Gamma$ through the lengths $d_i$ only.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ConsecutiveIntervals.lean#L57-L83 (`ConsistentSubmodular.Chains.left_eq_sum`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_EqualizingDistribution

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains
variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)
include hI

theorem ConsistentSubmodular.Chains.left_eq_sum (j : Fin (N + 1)) :
    I.left j = ∑ i, if i < j then intervalLength I i else 0 := by sorry
