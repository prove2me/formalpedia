-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_history_transition
-- name    : CountingLLL.ReciprocalTest.suppressed_history_transition
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:58:35.415674+00:00
-- url     : https://prove2.me/theorems/9144c645-e83f-440c-abdb-5d391b9d32da
-- title:
--   Markov transition law of the fully suppressed execution
-- statement:
--   For any event determined by the complete finite state history of the fully suppressed ReciprocalTest execution, the joint probability of that event, the current state, and a given next state factors into the history-and-current-state probability times the suppressed transition mass. This is the finite-history Markov property with no division by conditioning probabilities.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5; Markov law of the suppressed execution.

import Definitions.Def_CountingLLL_ReciprocalSuppressedTransition
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.suppressed_history_transition (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ)
    (H : (Fin (n+1) → State) → Prop) (s s' : State) :
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧
      allSuppressedRun ω n = s ∧ allSuppressedRun ω (n+1) = s'} =
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧
      allSuppressedRun ω n = s} * suppressedTransitionMass B s s' := by sorry
