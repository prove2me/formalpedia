-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_xiStar_le_adaptivityGap
-- name    : ConsistentSubmodular.Chains.xiStar_le_adaptivityGap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:00.194094+00:00
-- url     : https://prove2.me/theorems/4b4eefc7-e6ad-4a8c-8a1f-363c47606be8
-- title:
--   Lemma 4 — $\Gamma\ge\xi^\star$ for equalizing consecutive intervals
-- statement:
--   Let $I$ be an interval-selection instance with intervals $[\ell_0,r_0],\dots,[\ell_N,r_N]$ that is nonincreasing consecutive ($\ell_0=0$, $\ell_{i+1}=r_i$, lengths $r_i-\ell_i$ nonincreasing and the last one positive), and suppose the distribution $p$ on the intervals is equalizing (every fixed interval $i$ has the same expected value $\mathbb E_{j\sim p}[v(i,j)]$). Then its adaptivity gap $\Gamma(\ell,r,p)$ satisfies
--   $$\xi^\star\;\le\;\Gamma(\ell,r,p),$$
--   where $\xi^\star\approx0.7942$ is the root of $\Psi$ in $(1/2,1)$.
--
--   This is the bound part of Lemma 4. With $B=\mathbb E[\ell_j]$, $C=\mathbb E[d_j]$ and $q=(1-\xi^\star)/\xi^\star$, the claim reduces to $C-d_N\le q\,(B+d_N)$, which is the chain inequality (14) multiplied by $d_N$. Combined with the reduction of Lemma 3, it yields the existence of $\xi^\star$-addition-robust distributions.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ConsecutiveIntervals.lean#L209-L244 (`ConsistentSubmodular.Chains.xiStar_le_adaptivityGap`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)
  (hE : I.IsEqualizing)
include hI hE

theorem ConsistentSubmodular.Chains.xiStar_le_adaptivityGap : xiStar ≤ I.adaptivityGap := by sorry
