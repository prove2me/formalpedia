-- Prove2me | Theorems.Thm_ErschlerZheng_hasVolumeExponent_iff_tendsto_log_log_growth_div_log
-- name    : ErschlerZheng.hasVolumeExponent_iff_tendsto_log_log_growth_div_log
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:16:30.164459+00:00
-- url     : https://prove2.me/theorems/ccdfeb8b-3c77-49bc-a2d9-38f2be034829
-- title:
--   p. 58, bundle reading — the volume exponent along the integers is the limit over real r: log log v(n)/log n → α iff log log v(r)/log r → α
-- statement:
--   For every group $G$, every set $S \subseteq G$ and every real $\alpha$: `HasVolumeExponent S α`, which says that $\log\log v_{G,S}(n)/\log n$ tends to $\alpha$ as the integer $n$ tends to infinity, holds if and only if $\log\log v_{G,S}(r)/\log r$ tends to $\alpha$ as the real number $r$ tends to infinity. Here $v_{G,S}(r)$ is `growth S r`, the number of elements of `Chou.wordBall S ⌊r⌋₊`, and $\log$ is `Real.log`. The statement does not assume that $S$ is finite or generates $G$.
--
--   This is not a result of the paper. It backs the sentence of the Walks bundle note `ErschlerZheng_Walks` saying that the limit along the integers in `HasVolumeExponent` is the same as the limit over real $r$ of p. 58, which justifies stating that limit along the integers, as in the milestone `ErschlerZheng.hasVolumeExponent_firstString_alpha0`.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 58, the volume exponent along the integers and along the reals (supporting fact, not in the paper)

import Mathlib
import Definitions.Def_ErschlerZheng_Walks

namespace ErschlerZheng

theorem hasVolumeExponent_iff_tendsto_log_log_growth_div_log {G : Type*} [Group G] (S : Set G)
    (α : ℝ) :
    HasVolumeExponent S α ↔
      Filter.Tendsto (fun r : ℝ => Real.log (Real.log (growth S r)) / Real.log r) Filter.atTop
        (nhds α) := by
  sorry

end ErschlerZheng
