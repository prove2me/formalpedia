-- Prove2me | Theorems.Thm_ConsistentSubmodular_Checkpoints_subblock_count
-- name    : ConsistentSubmodular.Checkpoints.subblock_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:42.860268+00:00
-- url     : https://prove2.me/theorems/7a20d841-375b-4045-a87c-9dd063f0eeb5
-- title:
--   At most one subblock contains a fixed update strictly inside
-- statement:
--   Let $\ell,h,r\in\mathbb N$ with $h>0$. For $\sigma\in\{0,\dots,h-1\}$ let $\mathrm{lo}_\sigma=\lfloor\sigma\ell/h\rfloor$ and $\mathrm{hi}_\sigma=\lfloor(\sigma+1)\ell/h\rfloor$, so that subblock $\sigma$ consists of the updates $\mathrm{lo}_\sigma+1,\dots,\mathrm{hi}_\sigma$. Then
--   $$\frac{h-1}{h}\;\le\;\frac1h\sum_{\sigma=0}^{h-1}\Bigl(\mathbf 1[r\le \mathrm{lo}_\sigma]+\mathbf 1\bigl[r>\mathrm{lo}_\sigma\ \wedge\ \mathrm{hi}_\sigma\le r\bigr]\Bigr).$$
--
--   Equivalently, for at least $h-1$ of the $h$ subblocks, the update $r$ is either at or before the start of the subblock, or at or after its end. Hence, if the subblock is chosen uniformly at random, with probability at least $1-1/h$ the algorithm holds a full core at update $r$. This is used in the proof of Lemma 1.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/Checkpoints.lean#L191-L216 (`ConsistentSubmodular.Checkpoints.subblock_count`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointSchedule

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ} {α : ℝ}

theorem ConsistentSubmodular.Checkpoints.subblock_count (ℓ h r : ℕ) (hh : 0 < h) :
    ((h : ℝ) - 1) / h ≤
      (∑ σ : Fin h, ((if r ≤ lo ℓ h σ then 1 else 0) +
        (if ¬ r ≤ lo ℓ h σ ∧ hi ℓ h σ ≤ r then 1 else 0) : ℝ)) / h := by sorry
