-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_history_fresh
-- name    : CountingLLL.ReciprocalTest.suppressed_history_fresh
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:56:23.151191+00:00
-- url     : https://prove2.me/theorems/1992a8b3-05ee-4baf-979f-2b1a276afe30
-- title:
--   Fresh inputs conditional on the fully suppressed execution history
-- statement:
--   Fix a time and a state of the fully suppressed ReciprocalTest execution. For any event determined by the whole finite state history, if the current state selects an entropy coordinate, that coordinate retains its original marginal law jointly with the history and state. The unnormalized identity also holds when the history has probability zero.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5; fresh-input foundation for the suppressed-walk coupling.

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
import Definitions.Def_CountingLLL_ReciprocalAllSuppressed
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.suppressed_history_fresh (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ) (s : State) (a : ReadIndex)
    (ha : readIndex s = some a) (H : (Fin (n+1) → State) → Prop) (U : Set ℕ) :
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧
      allSuppressedRun ω n = s ∧ entropyCode ω a ∈ U} =
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧
      allSuppressedRun ω n = s} * readLaw B a U := by sorry
