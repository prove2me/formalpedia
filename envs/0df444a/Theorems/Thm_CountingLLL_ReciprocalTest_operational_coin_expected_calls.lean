-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_operational_coin_expected_calls
-- name    : CountingLLL.ReciprocalTest.operational_coin_expected_calls
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:26:56.202612+00:00
-- url     : https://prove2.me/theorems/c305cd3c-1151-45ff-bf32-804682bc7d40
-- title:
--   Operational Coin expected oracle-call count
-- statement:
--   For $0\le B\le1$, start the operational local Coin procedure on the independent oracle and fair-bit entropy streams. The expected number of oracle calls up to its first return is exactly $2/(2-B)$, interpreted in the extended nonnegative reals. This concerns one local Coin call, not the total number of calls made by the full ReciprocalTest.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6 and proof of Lemma 6.5, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_CoinCost
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.operational_coin_expected_calls (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    (∫⁻ ω, coinOracleCost ω ∂entropyLaw (ENNReal.ofReal B)) = ENNReal.ofReal (2/(2-B)) := by sorry
