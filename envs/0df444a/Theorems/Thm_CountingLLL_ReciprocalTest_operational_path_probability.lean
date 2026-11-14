-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_operational_path_probability
-- name    : CountingLLL.ReciprocalTest.operational_path_probability
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:38:08.088253+00:00
-- url     : https://prove2.me/theorems/3894119d-b238-4ed5-b64d-b605a25b1c3d
-- title:
--   Exact finite path probabilities of ReciprocalTest
-- statement:
--   For every finite prescribed sequence of states, the probability that the operational ReciprocalTest execution follows that sequence equals the indicator that the first prescribed state is the initial state, multiplied by the transition masses of all successive pairs. This is a complete finite-dimensional path law and is a tool for coupling the algorithm to the contracted walk.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5. This is an exact operational path-law ingredient for the source’s random-walk coupling.

import Definitions.Def_CountingLLL_ReciprocalTransition
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal BigOperators
open Classical

theorem CountingLLL.ReciprocalTest.operational_path_probability (B : ℝ≥0∞) (hB : B ≤ 1) (x : ℕ → State) (n : ℕ) :
    entropyLaw B {ω | ∀ j ≤ n, run ω j = x j} =
      (if x 0 = initial then 1 else 0) * ∏ j ∈ Finset.range n, transitionMass B (x j) (x (j+1)) := by sorry
