-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_coin_cost_measurable
-- name    : CountingLLL.ReciprocalTest.coin_cost_measurable
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:29:02.727571+00:00
-- url     : https://prove2.me/theorems/4d098f87-8592-4108-a0c6-ddcd3618064c
-- title:
--   Operational local Coin oracle cost is measurable
-- statement:
--   The number of oracle calls used before the first return of the operational local Coin procedure, with value infinity on nonreturning tapes, is a measurable function of the entropy streams.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6 and proof of Lemma 6.5, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_CoinCost
open MeasureTheory CountingLLL.ReciprocalTest

theorem CountingLLL.ReciprocalTest.coin_cost_measurable : Measurable coinOracleCost := by sorry
