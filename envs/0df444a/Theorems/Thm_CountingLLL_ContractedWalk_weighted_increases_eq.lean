-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_weighted_increases_eq
-- name    : CountingLLL.ContractedWalk.weighted_increases_eq
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:58:06.204307+00:00
-- url     : https://prove2.me/theorems/885ed4c7-808e-40fa-9cf7-401b6f5462fd
-- title:
--   Expected weighted upward changes factor by the upward probability
-- statement:
--   In the abstract contracted walk with upward probability $p$, the expected sum of reciprocal-counter weights over upward changes is $p$ times the expected sum over all active changes. In particular, when the initial level is three and the initial counter is two, the latter is the source quantity $M$.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedCost
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ContractedWalk.weighted_increases_eq (p : ℝ≥0∞) (hp : p ≤ 1) (i j : ℕ) :
    expectedWeightedIncreases p i j = expectedWeightedChanges p i j * p := by sorry
