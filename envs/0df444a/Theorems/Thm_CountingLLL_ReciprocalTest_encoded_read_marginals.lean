-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_encoded_read_marginals
-- name    : CountingLLL.ReciprocalTest.encoded_read_marginals
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:58:36.01747+00:00
-- url     : https://prove2.me/theorems/c65b69ab-ad1c-4f35-8095-81f88a7479bb
-- title:
--   Encoded oracle, fair-bit and uniform read probabilities
-- statement:
--   For an oracle probability $B\le1$, all encoded coordinate laws are probability measures. An oracle coordinate is zero with probability $B$, a fair-bit coordinate is one with probability $1/2$, and a uniform coordinate with range size $m+1$ is zero with probability $1/(m+1)$. These are the one-coordinate laws of the independent encoded reveal-machine input.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.encoded_read_marginals (B : ℝ≥0∞) (hB : B ≤ 1) :
    (∀ a, IsProbabilityMeasure (readLaw B a)) ∧
    (∀ i, readLaw B (.inl i) {0} = B) ∧
    (∀ i, readLaw B (.inr (.inl i)) {1} = 1/2) ∧
    (∀ a, readLaw B (.inr (.inr a)) {0} = 1/((a.1+1 : ℕ) : ℝ≥0∞)) := by sorry
