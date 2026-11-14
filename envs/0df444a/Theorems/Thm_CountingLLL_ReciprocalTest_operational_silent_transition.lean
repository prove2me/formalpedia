-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_operational_silent_transition
-- name    : CountingLLL.ReciprocalTest.operational_silent_transition
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:11:13.8062+00:00
-- url     : https://prove2.me/theorems/3d45ed09-bbf5-4df4-aee5-f35dac9c1845
-- title:
--   Operational silent-step transition law
-- statement:
--   For an operational ReciprocalTest state that makes no entropy query, the next state is deterministic: the probability of a state-and-next-state event is the state probability when the deterministic successor matches, and zero otherwise. These are one-step laws; eventual return and total expected cost are separate.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest CountingLLL.RevealMachine
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.operational_silent_transition (B : ℝ≥0∞) (n : ℕ) (s s' : State)
    (ha : readIndex s = none) :
    (step (uniformEntropy 0) s = s' →
      entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω n = s ∧ CountingLLL.ReciprocalTest.run ω (n+1) = s'} =
        entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω n = s}) ∧
    (step (uniformEntropy 0) s ≠ s' →
      entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω n = s ∧ CountingLLL.ReciprocalTest.run ω (n+1) = s'} = 0) := by sorry
