-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_isEqualizing_iff
-- name    : ConsistentSubmodular.Chains.isEqualizing_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:49.582402+00:00
-- url     : https://prove2.me/theorems/5f1453f2-bdda-40ff-9aa0-ccf444fd2d8a
-- title:
--   Equalizing distribution (5) as prefix sums $d_N/d_i$
-- statement:
--   Let $I$ be a nonincreasing consecutive interval instance with intervals $[\ell_i,r_i]$, lengths $d_i=r_i-\ell_i$ and probabilities $p_0,\dots,p_N$ ($i=0,\dots,N$). Then $p$ is equalizing, that is, every fixed interval $i$ has the same expected value $\mathbb E_{j\sim p}[v(i,j)]$, if and only if for every $i\in\{0,\dots,N\}$
--   $$\sum_{j\le i}p_j\;=\;\frac{d_N}{d_i}.$$
--
--   This gives the explicit form (5) of the equalizing distribution, which determines the probabilities from the lengths of the intervals. It is the basis of the computation of the adaptivity gap in Lemma 4.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/EqualizingDistribution.lean#L87-L104 (`ConsistentSubmodular.Chains.isEqualizing_iff`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_EqualizingDistribution

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains
variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)
include hI

theorem ConsistentSubmodular.Chains.isEqualizing_iff : I.IsEqualizing ↔
    ∀ i, ∑ j ∈ Finset.Iic i, I.prob j = intervalLength I (Fin.last N) / intervalLength I i := by sorry
