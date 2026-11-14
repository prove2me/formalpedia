-- Prove2me | Theorems.Thm_ConsistentSubmodular_Shadow_chain_fixedValue_le
-- name    : ConsistentSubmodular.Shadow.chain_fixedValue_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:43.366038+00:00
-- url     : https://prove2.me/theorems/78ef757c-4959-4c43-a912-ddbfd5f854ee
-- title:
--   Fixed value of the chain instance is at most $B+1$
-- statement:
--   Let $N\in\mathbb N$ and let $d_0\ge d_1\ge\dots\ge d_N=1$ be reals. Let $I$ be the interval instance with consecutive intervals $[\ell_j,\ell_j+d_j]$, where $\ell_j=\sum_{i<j}d_i$, for $j=0,\dots,N$, with the equalizing probabilities $p_0=1/d_0$ and $p_j=1/d_j-1/d_{j-1}$ for $j\ge1$ (so that $p_0+\dots+p_j=1/d_j$). Then its best fixed expected value satisfies
--   $$\max_i\,\mathbb E_{j\sim p}\bigl[v(i,j)\bigr]\;\le\;\sum_{j=0}^{N}p_j\,\ell_j+1 \;=\;B+1.$$
--
--   Interval $i$ gains $d_i$ exactly at the realizations $j\le i$ and nothing afterwards, so its expected value is $B+d_i(p_0+\dots+p_i)=B+1$. The bound is used in the chain bound (Lemma 3) to control the numerator of the adaptivity gap.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ShadowChains.lean#L148-L176 (`ConsistentSubmodular.Shadow.chain_fixedValue_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ShadowChains

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Shadow
variable {N : ℕ} {d : ℕ → ℝ}
variable (hd : ∀ j < N, d (j + 1) ≤ d j) (hN : d N = 1)

theorem ConsistentSubmodular.Shadow.chain_fixedValue_le :
    (chainInstance N d hd hN).fixedValue ≤
      ∑ j : Fin (N + 1), chainProb d j * chainLeft d j + 1 := by sorry
