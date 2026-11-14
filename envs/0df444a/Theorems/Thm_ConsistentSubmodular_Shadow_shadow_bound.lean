-- Prove2me | Theorems.Thm_ConsistentSubmodular_Shadow_shadow_bound
-- name    : ConsistentSubmodular.Shadow.shadow_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:17.831335+00:00
-- url     : https://prove2.me/theorems/6a1f5de9-6d52-4376-ac2a-6ff8aac7526d
-- title:
--   Shadow reduction — $\alpha\,\mathbb E[\max_i v]\le\max_i\mathbb E[v]$
-- statement:
--   Let $\alpha\in[0,1]$ and suppose that every instance of nonincreasing consecutive intervals with the equalizing distribution has adaptivity gap at least $\alpha$ (the hypothesis of Lemma 3). Then for every interval-selection instance $I$ with intervals $[\ell_i,r_i]$ and distribution $p$ on $\{0,\dots,N\}$, with values $v(i,j)=\ell_j+|[\ell_i,r_i]\cap[\ell_j,\infty)|$,
--   $$\alpha\;\mathbb E_{j\sim p}\Big[\max_i v(i,j)\Big]\;\le\;\max_i\,\mathbb E_{j\sim p}\big[v(i,j)\big],$$
--   that is, $\alpha\cdot(\text{value in hindsight})\le(\text{best fixed value})$.
--
--   This is the shadow reduction: it applies inequality (7) to the shadow intervals, with $M=\max_i\mathbb E_j|I_i\cap[\ell_j,\infty)|$ bounding their own values by (6). It yields the proof of Lemma 3 (reduction of the adaptivity gap to consecutive intervals).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ShadowIntervals.lean#L69-L95 (`ConsistentSubmodular.Shadow.shadow_bound`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ShadowChains

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Shadow
variable {N : ℕ} (I : IntervalInstance N)

theorem ConsistentSubmodular.Shadow.shadow_bound {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hchain : ChainHypothesis α) :
    α * I.adaptiveValue ≤ I.fixedValue := by sorry
