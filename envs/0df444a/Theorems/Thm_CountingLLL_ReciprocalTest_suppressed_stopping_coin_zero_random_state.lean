-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_stopping_coin_zero_random_state
-- name    : CountingLLL.ReciprocalTest.suppressed_stopping_coin_zero_random_state
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:14:40.778524+00:00
-- url     : https://prove2.me/theorems/68fd0f4f-1e46-4d8d-8026-29f45e8ee159
-- title:
--   Adaptive two-step Coin-zero probability with random state
-- statement:
--   At a finite history-adapted stopping time of the fully suppressed execution, suppose the current phase is a Coin-oracle phase in a fixed context, while the rest of the state may be random. The joint probability that the following two atomic transitions return zero is exactly B/2 times the probability of reaching that phase at the stopping time. The stopping time may be infinite, and no conditional-probability denominator is used.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Algorithm 6 and Lemma 6.5; strong-Markov progress ingredient for random Coin-call states.

import Definitions.Def_CountingLLL_ReciprocalSuppressedTransition
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.suppressed_stopping_coin_zero_random_state (B : ℝ≥0∞) (hB : B ≤ 1) (T : Entropy → Option ℕ)
    (H : (n : ℕ) → (Fin (n+1) → State) → Prop)
    (hT : ∀ ω n, T ω = some n ↔ H n (fun j => allSuppressedRun ω j.val)) (k : Context) :
    entropyLaw B {ω | ∃ n, T ω = some n ∧ (allSuppressedRun ω n).phase = .coinOracle k ∧
      let s := allSuppressedRun ω n
      let u : State := {s with oracleUsed := s.oracleUsed+1, phase := .coinFair k}
      let v : State := coinReturn k false {u with fairUsed := u.fairUsed+1}
      allSuppressedRun ω (n+1) = u ∧ allSuppressedRun ω (n+2) = v} =
    entropyLaw B {ω | ∃ n, T ω = some n ∧ (allSuppressedRun ω n).phase = .coinOracle k} * (B/2) := by sorry
