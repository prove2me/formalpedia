-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_loop_decrease
-- name    : CountingLLL.ReciprocalTest.suppressed_loop_decrease
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:07:28.115204+00:00
-- url     : https://prove2.me/theorems/df6bef46-92c2-473b-8ce9-9cdf63afd54b
-- title:
--   Positive chance of a counter decrease from a loop state
-- statement:
--   At any fully suppressed loop state with a positive first counter, the joint probability of an arbitrary finite past history and a decrease within three steps is at least B/2 times the probability of that history and state. The result is valid for all B at most one and does not divide by a conditioning probability.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, Algorithm 6 and Lemma 6.5; bounded-time progress toward almost-sure nonsticking.

import Definitions.Def_CountingLLL_ReciprocalSuppressedTransition
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.suppressed_loop_decrease (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ)
    (H : (Fin (n+1) → State) → Prop) (s : State)
    (hs : s.phase = .loop) (hi : 0 < s.i) :
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s} * (B/2) ≤
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s ∧
      (allSuppressedRun ω (n+3)).i < s.i} := by sorry
