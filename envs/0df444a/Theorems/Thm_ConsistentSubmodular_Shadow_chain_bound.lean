-- Prove2me | Theorems.Thm_ConsistentSubmodular_Shadow_chain_bound
-- name    : ConsistentSubmodular.Shadow.chain_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:06.901932+00:00
-- url     : https://prove2.me/theorems/8796670f-9da2-4740-a3c7-3f3a512e82a5
-- title:
--   The chain bound for consecutive intervals
-- statement:
--   Let $\alpha\ge0$ and suppose that every instance of nonincreasing consecutive intervals with the equalizing distribution has adaptivity gap at least $\alpha$ (for every $N$). Then for every $N\in\mathbb N$ and every sequence $d_0\ge d_1\ge\dots\ge d_N=1$ of reals,
--   $$\alpha\sum_{j=0}^{N-1}\Bigl(1-\frac{d_{j+1}}{d_j}\Bigr)\;\le\;(1-\alpha)\Bigl(1+\sum_{j=0}^{N-1}(d_j-1)\Bigr).$$
--
--   The inequality is the content of the gap hypothesis $\Gamma\ge\alpha$ rewritten for the chain of interval lengths, using the closed forms of $B$, $C$ and $\Gamma$ for equalizing consecutive intervals. It is the starting point of the shadow-chain argument that passes from discrete chains to a continuous inequality in the proof of Lemma 3 and the lower bound on $\xi^\star$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ShadowChains.lean#L193-L227 (`ConsistentSubmodular.Shadow.chain_bound`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ShadowChains

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Shadow

theorem ConsistentSubmodular.Shadow.chain_bound {α : ℝ} (hα : 0 ≤ α) (hchain : ChainHypothesis α) {N : ℕ} {d : ℕ → ℝ}
    (hd : ∀ j < N, d (j + 1) ≤ d j) (hN : d N = 1) :
    α * ∑ j ∈ Finset.range N, (1 - d (j + 1) / d j) ≤
      (1 - α) * (1 + ∑ j ∈ Finset.range N, (d j - 1)) := by sorry
