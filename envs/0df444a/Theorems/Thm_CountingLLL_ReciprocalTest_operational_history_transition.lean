-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_operational_history_transition
-- name    : CountingLLL.ReciprocalTest.operational_history_transition
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:35:36.757334+00:00
-- url     : https://prove2.me/theorems/a56eb4bf-93d0-4b7d-9690-4e63f57a0399
-- title:
--   ReciprocalTest satisfies the Markov transition law given its entire history
-- statement:
--   For any event determined by the complete finite state history of ReciprocalTest, the joint probability of that event, the current state, and a specified next state factors into the probability of the event and current state times the published operational transition mass. This is the full finite-history Markov property of the algorithm, stated without dividing by conditioning probabilities.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5. This is an operational Markov property supporting, but not itself proving, the paper’s coupling and cost analysis.

import Definitions.Def_CountingLLL_ReciprocalTransition
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.operational_history_transition (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ)
    (H : (Fin (n+1) → State) → Prop) (s s' : State) :
    entropyLaw B {ω | H (fun j => CountingLLL.ReciprocalTest.run ω j.val) ∧
      CountingLLL.ReciprocalTest.run ω n = s ∧ CountingLLL.ReciprocalTest.run ω (n+1) = s'} =
    entropyLaw B {ω | H (fun j => CountingLLL.ReciprocalTest.run ω j.val) ∧
      CountingLLL.ReciprocalTest.run ω n = s} * transitionMass B s s' := by sorry
