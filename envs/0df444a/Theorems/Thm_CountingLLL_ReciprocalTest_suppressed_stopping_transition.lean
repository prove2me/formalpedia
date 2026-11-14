-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_stopping_transition
-- name    : CountingLLL.ReciprocalTest.suppressed_stopping_transition
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:11:58.383835+00:00
-- url     : https://prove2.me/theorems/ff3fa23a-dd65-44da-8a84-e96587e6861c
-- title:
--   Suppressed execution transition law at stopping times
-- statement:
--   At any history-adapted optional stopping time of the fully suppressed ReciprocalTest, the joint mass of reaching a given current state and moving next to a given state equals the mass of reaching the current state times the suppressed transition mass. The stopping time may be infinite; no conditional-probability denominator or almost-sure termination assumption is required.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5; stopping-time transition tool for the adaptive contracted walk.

import Definitions.Def_CountingLLL_ReciprocalSuppressedTransition
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.suppressed_stopping_transition (B : ℝ≥0∞) (hB : B ≤ 1) (T : Entropy → Option ℕ)
    (H : (n : ℕ) → (Fin (n+1) → State) → Prop)
    (hT : ∀ ω n, T ω = some n ↔ H n (fun j => allSuppressedRun ω j.val)) (s s' : State) :
    entropyLaw B {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s ∧ allSuppressedRun ω (n+1) = s'} =
    entropyLaw B {ω | ∃ n, T ω = some n ∧ allSuppressedRun ω n = s} * suppressedTransitionMass B s s' := by sorry
