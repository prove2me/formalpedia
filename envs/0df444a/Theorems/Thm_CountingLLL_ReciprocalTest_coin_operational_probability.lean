-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_coin_operational_probability
-- name    : CountingLLL.ReciprocalTest.coin_operational_probability
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:02:59.558867+00:00
-- url     : https://prove2.me/theorems/1569633f-8dfb-4033-ab1b-bcf85a287fa8
-- title:
--   Operational Coin return-one probability
-- statement:
--   For $0\le B\le1$, execute the initial Coin call of Algorithm 6 in its small-step machine, using independent oracle, fair-bit and uniform-draw streams. The probability that the call returns one is exactly $2(1-B)/(2-B)$. This is the source’s Coin output claim applied to the actual operational semantics.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, Algorithm 6 and proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.coin_operational_probability (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    entropyLaw (ENNReal.ofReal B)
      {ω | ∃ t, ((step ω)^[t] ({phase := .coinOracle .initial} : State)).phase = .initialCheck} =
      ENNReal.ofReal (2*(1-B)/(2-B)) := by sorry
