-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_coin_zero_transition_masses
-- name    : CountingLLL.ReciprocalTest.suppressed_coin_zero_transition_masses
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:03:26.567551+00:00
-- url     : https://prove2.me/theorems/e0844f86-1e6d-4f79-9947-8bcb323bb1a9
-- title:
--   Transition masses for the two-step zero outcome of Coin
-- statement:
--   In any context of a fully suppressed Coin call, the oracle-false transition to the fair-bit phase has mass B, and the fair-true transition returning zero has mass one half. These identities apply to every state and identify the two transitions used to obtain a uniformly positive counter-decrease event.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, Algorithm 6 and Lemma 6.5, PDF pp. 27–28.

import Definitions.Def_CountingLLL_ReciprocalSuppressedTransition
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.suppressed_coin_zero_transition_masses (B : ℝ≥0∞) (hB : B ≤ 1) (s : State) (k : Context) :
    (s.phase = .coinOracle k →
      suppressedTransitionMass B s {s with oracleUsed := s.oracleUsed+1, phase := .coinFair k} = B) ∧
    (s.phase = .coinFair k →
      suppressedTransitionMass B s (coinReturn k false {s with fairUsed := s.fairUsed+1}) = 1/2) := by sorry
