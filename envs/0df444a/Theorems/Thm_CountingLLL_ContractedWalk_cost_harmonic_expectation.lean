-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_cost_harmonic_expectation
-- name    : CountingLLL.ContractedWalk.cost_harmonic_expectation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:01:03.390537+00:00
-- url     : https://prove2.me/theorems/4238e656-2503-4a0a-8b08-c575fa26d339
-- title:
--   Source weighted-change expectation is a harmonic expectation
-- statement:
--   For $0\leq\theta<1/3$, let $M$ be the expected sum of reciprocal counters over all changes in the abstract contracted walk starting at level three and counter two, and let $U_3$ be its number of upward changes before absorption. Then $$\theta M=\mathbb E\!\left[\sum_{k=0}^{U_3-1}\frac1{k+2}\right].$$ The equality is in extended nonnegative reals and is the probabilistic reduction used in the source oracle-cost argument.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
import Definitions.Def_CountingLLL_ContractedCost
open MeasureTheory CountingLLL.ContractedWalk
open scoped BigOperators ENNReal

theorem CountingLLL.ContractedWalk.cost_harmonic_expectation (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1/3) :
    expectedWeightedChanges (ENNReal.ofReal θ) 3 2 * ENNReal.ofReal θ =
      ∫⁻ ω, ∑ k ∈ Finset.range (upwardCount ω 3), (((2+k : ℕ) : ℝ≥0∞)⁻¹) ∂tapeLaw (ENNReal.ofReal θ) := by sorry
