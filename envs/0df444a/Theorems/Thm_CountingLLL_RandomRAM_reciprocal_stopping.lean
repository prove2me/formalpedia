-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_reciprocal_stopping
-- name    : CountingLLL.RandomRAM.reciprocal_stopping
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:33:31.560435+00:00
-- url     : https://prove2.me/theorems/4a5e08ba-5b2c-45e7-afbe-ec89ddcf0926
-- title:
--   Geometric stopping time of the reciprocal estimator
-- statement:
--   Let an infinite stream consist of independent samples from a probability law nu on the reals, and let tau be the probability that one sample is nonzero. The probability that the first n samples are all nonzero is tau^n. If tau<1, the stream reaches zero almost surely. The expected number of requested samples, including the first zero, is 1/(1-tau), interpreted in the extended nonnegative reals. On a stream whose first zero occurs at index k (starting from zero), the sample count is exactly k+1. This proves the stopping and sample-count portion of the zero-terminated reciprocal series lemma; it does not yet prove the reciprocal output moment or cost claims.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, Lemma 5.4, Section 5.2.1, PDF p.18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

theorem CountingLLL.RandomRAM.reciprocal_stopping (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (∀ n : ℕ, (Measure.infinitePi fun _ : ℕ => ν) {ω | ∀ i < n, ω i ≠ 0} =
      ν {x | x ≠ 0} ^ n) ∧
    (ν {x | x ≠ 0} < 1 → ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => ν), ∃ n, ω n = 0) ∧
    (∫⁻ ω, ∑' n : ℕ, ({ω' : ℕ → ℝ | ∀ i < n, ω' i ≠ 0}).indicator 1 ω
      ∂(Measure.infinitePi fun _ : ℕ => ν)) = (1 - ν {x | x ≠ 0})⁻¹ ∧
    (∀ (ω : ℕ → ℝ) (k : ℕ), ω k = 0 → (∀ j < k, ω j ≠ 0) →
      (∑' n : ℕ, ({ω' : ℕ → ℝ | ∀ i < n, ω' i ≠ 0}).indicator (1 : (ℕ → ℝ) → ℝ≥0∞) ω) = (k + 1 : ℕ)) := by sorry
