-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_lemma_6_5_output_and_oracle
-- name    : CountingLLL.ReciprocalTest.lemma_6_5_output_and_oracle
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T06:40:38.262199+00:00
-- url     : https://prove2.me/theorems/98f935ab-2bbd-49ab-977f-c414692636a9
-- title:
--   ReciprocalTest output and oracle-call bounds
-- statement:
--   Let $B$ satisfy $e^{-3/10}\le B\le 1$, and execute Algorithm 6 with independent oracle answers that equal zero with probability $B$, independent fair bits, and independent uniform finite draws. The algorithm terminates almost surely, returns one with probability $1/(2B)$, and uses at most $3/B$ oracle calls in expectation. Oracle cost is infinite on nontermination. This target formalizes the output, termination and oracle-cost claims of Lemma 6.5; the additional expected bit-operation bound remains to be formalized using an implementation of the uniform-draw primitive.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, Lemma 6.5 and Algorithm 6, PDF pp. 26–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open MeasureTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.lemma_6_5_output_and_oracle (B : ℝ)
    (hB : Real.exp (-(3/10 : ℝ)) ≤ B) (hB1 : B ≤ 1) :
    let μ := entropyLaw (ENNReal.ofReal B)
    μ {ω | Returns ω true} = ENNReal.ofReal (1 / (2 * B)) ∧
    μ {ω | ¬ Halts ω} = 0 ∧
    (∫⁻ ω, oracleCost ω ∂μ) ≤ ENNReal.ofReal (3 / B) := by
  sorry
