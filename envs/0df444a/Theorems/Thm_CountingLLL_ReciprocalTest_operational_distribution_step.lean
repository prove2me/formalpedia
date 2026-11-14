-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_operational_distribution_step
-- name    : CountingLLL.ReciprocalTest.operational_distribution_step
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:16:23.995984+00:00
-- url     : https://prove2.me/theorems/8b729d1d-71d6-477a-81e0-01c9f1b2095f
-- title:
--   Countable-state distribution recursion for operational ReciprocalTest
-- statement:
--   Under the original entropy law with $B\le1$, let $K_B(s,s')$ be the explicitly defined one-step transition mass of the operational ReciprocalTest. For every step $n$ and state $s',$$\Pr(S_{n+1}=s')=\sum_s\Pr(S_n=s)K_B(s,s').$$ The sum is over all operational states. The theorem proves the finite-step distribution recursion; solving its eventual return and expected-cost equations is separate.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTransition
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest CountingLLL.RevealMachine
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.operational_distribution_step (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ) (s' : State) :
    entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω (n+1) = s'} =
      ∑' s : State, entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω n = s} * transitionMass B s s' := by sorry
