-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_source_M_bound
-- name    : CountingLLL.ContractedWalk.source_M_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:13:18.268356+00:00
-- url     : https://prove2.me/theorems/1559f36a-114e-4eef-bed0-96c014d97d56
-- title:
--   Source reciprocal-test weighted walk cost satisfies M < 74/25
-- statement:
--   For $0\le\theta\le9/40$, let $M$ be the expected sum of reciprocal-counter weights before changes of the abstract contracted walk started at level three and counter two. Then $$M<\frac{74}{25}.$$ This is the sharp numerical bound required in the paper’s oracle-call analysis. Connecting that abstract walk to the operational ReciprocalTest and deriving the full expected-call formula are separate results.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, calls to O, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedCost
open MeasureTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ContractedWalk.source_M_bound (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 9/40) :
    expectedWeightedChanges (ENNReal.ofReal θ) 3 2 < ENNReal.ofReal (74/25 : ℝ) := by sorry
