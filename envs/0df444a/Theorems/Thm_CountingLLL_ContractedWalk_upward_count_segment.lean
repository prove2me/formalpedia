-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_upward_count_segment
-- name    : CountingLLL.ContractedWalk.upward_count_segment
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:56:28.586624+00:00
-- url     : https://prove2.me/theorems/634722ed-3b08-4c05-874e-4272004674bd
-- title:
--   Contracted-walk upward counts split at the first unit hit
-- statement:
--   For a contracted-walk path from level $m+1$, split at the first time the coupled walk from level one reaches zero. If both that unit path and the remaining shifted path from level $m$ reach zero, the total number of upward moves is the sum of their upward counts. This is the pathwise segmentation used to factor the paper’s generating functions.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
open CountingLLL.ContractedWalk

theorem CountingLLL.ContractedWalk.upward_count_segment (ω : Tape) (m : ℕ) (h : ∃ t, level ω 1 t = 0) (hrest : ∃ t, level (fun k => ω (k+stopTime ω 1)) m t = 0) : upwardCount ω (m+1) = upwardCount ω 1 + upwardCount (fun k => ω (k+stopTime ω 1)) m := by sorry
