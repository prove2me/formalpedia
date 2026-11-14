-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_transitionMass_sum
-- name    : CountingLLL.ReciprocalTest.transitionMass_sum
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:17:53.141222+00:00
-- url     : https://prove2.me/theorems/a036512e-6b61-4728-ad51-5ea84f2994d8
-- title:
--   ReciprocalTest transition masses sum to one
-- statement:
--   For $B\le1$, the one-step transition masses of the operational ReciprocalTest sum to one from every state. Querying steps push a probability measure forward through a deterministic successor map; silent steps have a single successor.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTransition
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.transitionMass_sum (B : ℝ≥0∞) (hB : B ≤ 1) (s : State) :
    (∑' s' : State, transitionMass B s s') = 1 := by sorry
