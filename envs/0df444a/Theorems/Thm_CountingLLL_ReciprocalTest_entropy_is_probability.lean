-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_entropy_is_probability
-- name    : CountingLLL.ReciprocalTest.entropy_is_probability
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:40:40.335524+00:00
-- url     : https://prove2.me/theorems/e5f087ad-0e89-4bef-8593-4c95f21e7ec4
-- title:
--   ReciprocalTest entropy law is a probability measure
-- statement:
--   For every $B\in[0,1]$, the joint law of independent Bernoulli oracle answers, independent fair bits, and independent uniform finite draws used by Algorithm 6 is a probability measure. This establishes that the execution model is nondegenerate.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, Algorithm 6, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open MeasureTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.entropy_is_probability (B : ℝ≥0∞) (hB : B ≤ 1) : IsProbabilityMeasure (entropyLaw B) := by sorry
