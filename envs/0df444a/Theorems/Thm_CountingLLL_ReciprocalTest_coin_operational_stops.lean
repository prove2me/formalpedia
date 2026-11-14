-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_coin_operational_stops
-- name    : CountingLLL.ReciprocalTest.coin_operational_stops
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:10:44.169647+00:00
-- url     : https://prove2.me/theorems/0131fe90-abb7-4752-b57f-84ea2447cbca
-- title:
--   Operational Coin terminates almost surely
-- statement:
--   For $0\le B\le1$, the initial call to Coin in Algorithm 6 reaches one of its two return continuations with probability one under the small-step entropy law. This establishes almost-sure termination of that local procedure; it does not by itself establish termination of the entire ReciprocalTest.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, Algorithm 6 lines 1–7, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.coin_operational_stops (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    entropyLaw (ENNReal.ofReal B)
      {ω | ∃ t, ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase = .initialCheck ∨
                 ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase = .loop} = 1 := by sorry
