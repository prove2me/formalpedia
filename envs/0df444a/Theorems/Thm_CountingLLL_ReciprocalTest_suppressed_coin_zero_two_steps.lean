-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_coin_zero_two_steps
-- name    : CountingLLL.ReciprocalTest.suppressed_coin_zero_two_steps
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:03:30.319048+00:00
-- url     : https://prove2.me/theorems/82a186fb-ff81-41b8-a254-90e3881741f5
-- title:
--   Conditional probability of a two-step zero Coin outcome
-- statement:
--   In the fully suppressed execution, condition on an arbitrary finite state-history event and a current Coin-oracle state in any Coin context. The joint probability that the next oracle answer is false and the next fair bit is true, producing a zero Coin return in exactly two atomic steps, is the history-and-state probability multiplied by B/2. The identity avoids division and includes probability-zero histories.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, Algorithm 6 and Lemma 6.5; local progress ingredient for almost-sure nonsticking.

import Definitions.Def_CountingLLL_ReciprocalSuppressedTransition
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.suppressed_coin_zero_two_steps (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ)
    (H : (Fin (n+1) → State) → Prop) (s : State) (k : Context)
    (hs : s.phase = .coinOracle k) :
    let u : State := {s with oracleUsed := s.oracleUsed+1, phase := .coinFair k}
    let v : State := coinReturn k false {u with fairUsed := u.fairUsed+1}
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s ∧
      allSuppressedRun ω (n+1) = u ∧ allSuppressedRun ω (n+2) = v} =
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s} * (B/2) := by sorry
