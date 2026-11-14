-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_deterministic_transition_masses
-- name    : CountingLLL.ReciprocalTest.suppressed_deterministic_transition_masses
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:07:08.004206+00:00
-- url     : https://prove2.me/theorems/eeccda3c-becd-4f78-8813-acf810d59272
-- title:
--   Deterministic transitions of the suppressed loop
-- statement:
--   In the fully suppressed execution, a main-loop state with positive counter enters the first Coin call with probability one. A suppressed uniform-return check advances to the loop with probability one while consuming its uniform coordinate. These atomic transition identities support the bounded-time progress argument.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, Algorithm 6 and Lemma 6.5, PDF pp. 27–28.

import Definitions.Def_CountingLLL_ReciprocalSuppressedTransition
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.suppressed_deterministic_transition_masses (B : ℝ≥0∞) (hB : B ≤ 1) (s : State) :
    (s.phase = .loop → 0 < s.i →
      suppressedTransitionMass B s {s with phase := .coinOracle .first} = 1) ∧
    (s.phase = .uniformCheck →
      suppressedTransitionMass B s {s with uniformUsed := s.uniformUsed+1, phase := .loop} = 1) := by sorry
