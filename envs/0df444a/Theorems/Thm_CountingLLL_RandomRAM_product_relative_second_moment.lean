-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_product_relative_second_moment
-- name    : CountingLLL.RandomRAM.product_relative_second_moment
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:11:25.646426+00:00
-- url     : https://prove2.me/theorems/65f88762-6943-4c52-8b03-9dcb1925a6bc
-- title:
--   Relative second moment of an independent product
-- statement:
--   For a finite family of independent real random variables with finite second moments and nonzero means, the second moment of their product divided by the square of the product of their means is exactly the product over factors of one plus variance divided by squared mean. It is bounded by the exponential of the sum of these relative variances. This is the probabilistic factorization and exponential estimate used in the proof of equation (34) for randomized counting.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Theorem 1.3, Section 5.3, equation (34), PDF p.21, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem CountingLLL.RandomRAM.product_relative_second_moment {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hind : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) ≠ 0) :
    (∫ ω, (∏ i, X i ω) ^ 2 ∂μ) / (∏ i, ∫ ω, X i ω ∂μ) ^ 2 =
      ∏ i, (1 + variance (X i) μ / (∫ ω, X i ω ∂μ) ^ 2) ∧
    (∫ ω, (∏ i, X i ω) ^ 2 ∂μ) / (∏ i, ∫ ω, X i ω ∂μ) ^ 2 ≤
      Real.exp (∑ i, variance (X i) μ / (∫ ω, X i ω ∂μ) ^ 2) := by sorry
