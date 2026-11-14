-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_adaptivityGap_eq
-- name    : ConsistentSubmodular.Chains.adaptivityGap_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:16.425545+00:00
-- url     : https://prove2.me/theorems/cc11b215-f69c-4e67-9020-1093605ac859
-- title:
--   Adaptivity gap $\Gamma=(B+d_N)/(B+C)$ for equalizing consecutive intervals
-- statement:
--   Let $I$ be a nonincreasing consecutive interval instance with intervals $[\ell_j,r_j]$, lengths $d_j=r_j-\ell_j$ ($j=0,\dots,N$) and equalizing probabilities $p_j$. Put $B=\sum_j p_j\ell_j$ and $C=\sum_j p_j d_j$. Then the adaptivity gap $\Gamma$ of $I$ satisfies
--   $$\Gamma\;=\;\frac{B+d_N}{B+C}.$$
--
--   The adaptivity gap is the ratio of the best fixed expected value to the expected value in hindsight; for equalizing consecutive intervals these are $B+d_N$ and $B+C$ respectively. This closed form reduces the bound $\Gamma\ge\xi^\star$ of Lemma 4 to an inequality between $B$, $C$ and $d_N$.
--
--   **Formalization Note** The Lean definition of the gap is the ratio with the convention $\Gamma=1$ when the denominator vanishes; the statement is an equality in either case.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ConsecutiveIntervals.lean#L104-L122 (`ConsistentSubmodular.Chains.adaptivityGap_eq`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_EqualizingDistribution

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains
variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)
  (hE : I.IsEqualizing)
include hI hE

theorem ConsistentSubmodular.Chains.adaptivityGap_eq : I.adaptivityGap =
    (∑ j, I.prob j * I.left j + intervalLength I (Fin.last N)) /
      (∑ j, I.prob j * I.left j + ∑ j, I.prob j * intervalLength I j) := by sorry
