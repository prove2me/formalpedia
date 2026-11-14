-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_coin_probability
-- name    : CountingLLL.ReciprocalTest.coin_probability
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:52:01.865956+00:00
-- url     : https://prove2.me/theorems/5695098c-28f3-449a-ad57-a879a5820aef
-- title:
--   Algorithm 6 Coin output probability
-- statement:
--   For $0\le B\le1$, let each independent trial consist of an oracle bit that equals zero with probability $B$ and an independent fair bit. Repeat after a zero oracle bit and a zero fair bit; return zero after a zero oracle bit and a one fair bit; return one upon a one oracle bit. The probability of returning one is $2(1-B)/(2-B)$. This is the paper’s local Coin calculation, represented directly as an IID first-exit event; connecting it to the small-step execution is a separate task.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, Algorithm 6 and proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.coin_probability (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    let ν := (oracleLaw (ENNReal.ofReal B)).prod fairLaw
    let μ := Measure.infinitePi fun _ : ℕ => ν
    μ {ω : ℕ → Bool × Bool | ∃ n, (∀ i < n, ω i = (false, false)) ∧ (ω n).1 = true} =
      ENNReal.ofReal (2 * (1 - B) / (2 - B)) := by sorry
