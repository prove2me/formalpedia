-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_weighted_increases_harmonic
-- name    : CountingLLL.ContractedWalk.weighted_increases_harmonic
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:58:08.016205+00:00
-- url     : https://prove2.me/theorems/e87e3019-f146-49d2-bef7-56b430fbea85
-- title:
--   Weighted upward changes form a harmonic sum
-- statement:
--   If the abstract contracted walk is absorbed, and $U$ is its total number of upward changes, then the total reciprocal-counter weight over upward changes equals $\sum_{k=0}^{U-1}1/(j+k)$, where $j$ is the initial counter. The statement holds pathwise for any initial level and counter.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedCost
import Definitions.Def_CountingLLL_ContractedGF
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal BigOperators

theorem CountingLLL.ContractedWalk.weighted_increases_harmonic (ω : Tape) (i j : ℕ)
    (h : ∃ t, level ω i t = 0) :
    weightedIncreases ω i j = ∑ k ∈ Finset.range (upwardCount ω i), (((j+k : ℕ) : ℝ≥0∞)⁻¹) := by sorry
