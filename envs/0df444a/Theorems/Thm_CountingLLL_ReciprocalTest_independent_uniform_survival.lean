-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_independent_uniform_survival
-- name    : CountingLLL.ReciprocalTest.independent_uniform_survival
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:36:46.678471+00:00
-- url     : https://prove2.me/theorems/16a3826e-60c0-4a51-8a0d-095ad6cc1628
-- title:
--   Survival probability for independent uniform return tests
-- statement:
--   For each $i\geq0$, independently draw a uniform value from a set of $i+2$ elements with one distinguished element. The probability that none of the first $n$ draws selects its distinguished element is $1/(n+1)$. These independent uniform tests are the tests associated with successive counter values $2,\ldots,n+1$ in the paper’s suppressed-return analysis; linking their indexed draws to the machine execution remains separate.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, correctness, p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open CountingLLL.ReciprocalTest MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.independent_uniform_survival (n : ℕ) : (Measure.infinitePi fun i : ℕ => uniformLaw (i+1)) {ω : (i : ℕ) → Fin (i+2) | ∀ i < n, (ω i).val ≠ 0} = 1/(n+1 : ℝ≥0∞) := by sorry
