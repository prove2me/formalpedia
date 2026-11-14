-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_stopping_coin_zero
-- name    : CountingLLL.ReciprocalTest.suppressed_stopping_coin_zero
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:12:58.475225+00:00
-- url     : https://prove2.me/theorems/d5b8fcb9-b72a-485a-b2a7-4592b462385e
-- title:
--   Two-step zero Coin probability at adapted stopping times
-- statement:
--   At any history-adapted optional stopping time for the fully suppressed execution, conditional in joint-probability form on reaching a specified Coin-oracle state, the probability of a zero Coin return in the next two atomic steps is exactly B/2. The stopping time may be infinite, and the identity is valid for every Coin context.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Algorithm 6 and Lemma 6.5; adaptive progress ingredient for the contracted walk.

import Definitions.Def_CountingLLL_ReciprocalSuppressedTransition
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.suppressed_stopping_coin_zero (B : ℝ≥0∞) (hB : B ≤ 1) (T : Entropy → Option ℕ)
    (H : (n : ℕ) → (Fin (n+1) → State) → Prop)
    (hT : ∀ ω n, T ω = some n ↔ H n (fun j => allSuppressedRun ω j.val))
    (s : State) (k : Context) (hs : s.phase = .coinOracle k) :
    let u : State := {s with oracleUsed := s.oracleUsed+1, phase := .coinFair k}
    let v : State := coinReturn k false {u with fairUsed := u.fairUsed+1}
    entropyLaw B {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s ∧
      allSuppressedRun ω (n+1) = u ∧ allSuppressedRun ω (n+2) = v} =
    entropyLaw B {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s} * (B/2) := by sorry
