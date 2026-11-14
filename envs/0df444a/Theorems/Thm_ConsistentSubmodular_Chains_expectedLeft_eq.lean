-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_expectedLeft_eq
-- name    : ConsistentSubmodular.Chains.expectedLeft_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:53.920907+00:00
-- url     : https://prove2.me/theorems/ade6ff03-d20e-4f67-a1ff-dbae220ef058
-- title:
--   Expected left endpoint $B=\sum_{j<N}(d_j-d_N)$
-- statement:
--   Let $I$ be a nonincreasing consecutive interval instance with intervals $[\ell_j,r_j]$, lengths $d_j=r_j-\ell_j$ for $j=0,\dots,N$, and equalizing probabilities $p_j$. Then
--   $$B=\sum_{j=0}^{N}p_j\,\ell_j\;=\;\sum_{j=0}^{N-1}\bigl(d_j-d_N\bigr).$$
--
--   The expected left endpoint $B$ is thus determined by the lengths of the intervals alone. This identity, together with $\ell_j=\sum_{i<j}d_i$ and $\sum_{j\le i}p_j=d_N/d_i$, is used to write the adaptivity gap in terms of the chain $d_0\ge\dots\ge d_N$ in Lemma 4.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ConsecutiveIntervals.lean#L176-L207 (`ConsistentSubmodular.Chains.expectedLeft_eq`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_EqualizingDistribution

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains
variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)
  (hE : I.IsEqualizing)
include hI hE

theorem ConsistentSubmodular.Chains.expectedLeft_eq : ∑ j, I.prob j * I.left j =
    ∑ j : Fin N, (intervalLength I j.castSucc - intervalLength I (Fin.last N)) := by sorry
