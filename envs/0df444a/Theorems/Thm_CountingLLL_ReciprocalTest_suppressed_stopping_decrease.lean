-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_stopping_decrease
-- name    : CountingLLL.ReciprocalTest.suppressed_stopping_decrease
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T11:18:01.797469+00:00
-- url     : https://prove2.me/theorems/29b7c78b-c407-4cf2-b87f-ff1f2c02bc5e
-- title:
--   Uniform counter-decrease probability at adapted Coin calls
-- statement:
--   Consider any history-adapted optional stopping time at which the fully suppressed execution has a positive first counter. The probability that it stops in a first-Coin oracle phase and the counter decreases during the next two steps is at least B/2 times the probability that it stops in that phase. The current counter values and entropy offsets may be random, and the stopping time may be infinite.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, Algorithm 6 and §6.2, Lemma 6.5; adaptive progress toward almost-sure nonsticking.

import Definitions.Def_CountingLLL_ReciprocalSuppressedTransition
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.suppressed_stopping_decrease (B : ℝ≥0∞) (hB : B ≤ 1) (T : Entropy → Option ℕ)
    (H : (n : ℕ) → (Fin (n+1) → State) → Prop)
    (hT : ∀ ω n, T ω = some n ↔ H n (fun j => allSuppressedRun ω j.val))
    (hpos : ∀ ω n, T ω = some n → 0 < (allSuppressedRun ω n).i) :
    entropyLaw B {ω | ∃ n, T ω = some n ∧ (allSuppressedRun ω n).phase = .coinOracle .first} * (B/2) ≤
    entropyLaw B {ω | ∃ n, T ω = some n ∧ (allSuppressedRun ω n).phase = .coinOracle .first ∧
      (allSuppressedRun ω (n+2)).i < (allSuppressedRun ω n).i} := by sorry
