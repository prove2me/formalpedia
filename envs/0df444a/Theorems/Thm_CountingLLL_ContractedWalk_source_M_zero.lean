-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_source_M_zero
-- name    : CountingLLL.ContractedWalk.source_M_zero
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:09:47.847295+00:00
-- url     : https://prove2.me/theorems/d12cfcb3-5bef-429a-b8f1-e418d4347ebb
-- title:
--   Weighted reciprocal-test walk cost at zero upward probability
-- statement:
--   When the contracted walk has upward probability zero and starts at level three with counter two, its expected sum of reciprocal-counter weights is $M=3/2$.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedCost
open MeasureTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ContractedWalk.source_M_zero : expectedWeightedChanges 0 3 2 = (3:ℝ≥0∞)/2 := by sorry
