-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_coin_expected_calls
-- name    : CountingLLL.ReciprocalTest.coin_expected_calls
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:53:50.932023+00:00
-- url     : https://prove2.me/theorems/0d5a5778-0ac5-4238-b500-af19c86acb37
-- title:
--   Algorithm 6 Coin expected oracle calls
-- statement:
--   For $0\le B\le1$, let Coin repeat independent trials while the oracle returns zero and an independent fair bit returns zero. Each trial uses one oracle call. Then the expected number of oracle calls is $2/(2-B)$. The theorem models the trial sequence directly; its identification with the state machine is a separate task.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.coin_expected_calls (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    let ν := (oracleLaw (ENNReal.ofReal B)).prod fairLaw
    let μ := Measure.infinitePi fun _ : ℕ => ν
    (∫⁻ ω, ∑' n : ℕ, ({ω' : ℕ → Bool × Bool | ∀ i < n, ω' i = (false, false)}).indicator (1 : (ℕ → Bool × Bool) → ℝ≥0∞) ω ∂μ) =
      ENNReal.ofReal (2 / (2 - B)) := by sorry
