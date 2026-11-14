-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_right_le_left
-- name    : ConsistentSubmodular.Chains.right_le_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:51.700534+00:00
-- url     : https://prove2.me/theorems/832a4f60-6a99-40b4-9e43-60a528dd97dc
-- title:
--   Intervals of a nonincreasing consecutive instance are ordered
-- statement:
--   Let $I$ be an interval-selection instance with intervals $[\ell_0,r_0],\dots,[\ell_N,r_N]$ that is nonincreasing consecutive, that is, $\ell_0=0$, $\ell_{i+1}=r_i$ for $i<N$, the lengths $r_i-\ell_i$ are nonincreasing in $i$, and $r_N-\ell_N>0$. Then for all indices $i<j$ in $\{0,\dots,N\}$,
--   $$r_i\;\le\;\ell_j.$$
--
--   The intervals are therefore laid out left to right without overlap. This elementary fact is used in the computations of the adaptivity gap for consecutive intervals (Lemma 4).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/EqualizingDistribution.lean#L52-L64 (`ConsistentSubmodular.Chains.right_le_left`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)
include hI

theorem ConsistentSubmodular.Chains.right_le_left {i j : Fin (N + 1)} (hij : i < j) : I.right i ≤ I.left j := by sorry
