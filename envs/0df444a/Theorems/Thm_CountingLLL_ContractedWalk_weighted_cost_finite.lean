-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_weighted_cost_finite
-- name    : CountingLLL.ContractedWalk.weighted_cost_finite
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:02:47.916316+00:00
-- url     : https://prove2.me/theorems/19299011-0b62-4b67-923c-5990f7eecfde
-- title:
--   Weighted contracted-walk cost has finite expectation
-- statement:
--   For $0\le\theta<1/3$, a contracted walk started at level $i$ with initial counter $j\ge1$ has expected total reciprocal-counter change weight at most $i/(1-3\theta)$. In particular, the source weighted-change quantity $M$ is finite.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedCost
open MeasureTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ContractedWalk.weighted_cost_finite (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1/3) (i j : ℕ) (hj : 1 ≤ j) :
    expectedWeightedChanges (ENNReal.ofReal θ) i j ≤ ENNReal.ofReal ((i : ℝ)/(1-3*θ)) := by sorry
