-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_product_estimator_accuracy
-- name    : CountingLLL.RandomRAM.product_estimator_accuracy
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:17:40.269357+00:00
-- url     : https://prove2.me/theorems/917b3d9b-e30e-44ff-94fd-d9e2d6b02cde
-- title:
--   Relative accuracy of an independent product estimator
-- statement:
--   Let X_i be a finite independent family of real random variables, each square-integrable with nonzero mean, and suppose the product of the means is positive. Let a>0 and 0<epsilon<=1. If the sum of variance(X_i)/(E X_i)^2 is at most epsilon^2/20, then the scaled product estimator a times the product of the X_i lies within relative error epsilon of a times the product of their means with probability at least 15/16. The proof establishes square-integrability of the product from independence and the individual second moments. This is the probabilistic implication used for equation (34) in the proof of randomized approximate counting; applying it to the paper estimator additionally requires the source-specific marginal-estimator moment bounds.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Theorem 1.3, Section 5.3, equation (34), PDF p.21, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

theorem CountingLLL.RandomRAM.product_estimator_accuracy {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (a ε : ℝ)
    (ha : 0 < a) (hind : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) ≠ 0)
    (hZ : 0 < ∏ i, ∫ ω, X i ω ∂μ)
    (he0 : 0 < ε) (he1 : ε ≤ 1)
    (hbudget : (∑ i, variance (X i) μ / (∫ ω, X i ω ∂μ) ^ 2) ≤ ε ^ 2 / 20) :
    (15 / 16 : ℝ≥0∞) ≤ μ {ω |
      (1 - ε) * (a * (∏ i, ∫ ω, X i ω ∂μ)) ≤ a * (∏ i, X i ω) ∧
      a * (∏ i, X i ω) ≤ (1 + ε) * (a * (∏ i, ∫ ω, X i ω ∂μ))} := by sorry
