-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_absorption_and_expected_changes
-- name    : CountingLLL.ContractedWalk.absorption_and_expected_changes
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:22:19.383903+00:00
-- url     : https://prove2.me/theorems/5eeafb39-30ad-4f43-a32f-ab96e49f00cd
-- title:
--   Contracted walk absorption and expected change count
-- statement:
--   For $0\le\theta<1/3$, the absorbed walk that moves down by one with probability $1-\theta$ and up by two with probability $\theta$ reaches zero almost surely. Starting from level $i$, its expected number of changes is at most $i/(1-3\theta)$. This is the source’s contracted-walk hitting-time estimate.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedWalk
open MeasureTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ContractedWalk.absorption_and_expected_changes (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3) (i : ℕ) :
    tapeLaw (ENNReal.ofReal θ) {ω | ∃ t, level ω i t = 0} = 1 ∧
    expectedChanges (ENNReal.ofReal θ) i ≤ ENNReal.ofReal ((i : ℝ) / (1-3*θ)) := by sorry
