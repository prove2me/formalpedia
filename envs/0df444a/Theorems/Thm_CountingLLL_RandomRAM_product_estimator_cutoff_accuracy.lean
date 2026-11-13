-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_product_estimator_cutoff_accuracy
-- name    : CountingLLL.RandomRAM.product_estimator_cutoff_accuracy
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:19:04.017768+00:00
-- url     : https://prove2.me/theorems/0d5081bc-657e-4701-8a62-a8349fad0eec
-- title:
--   Accuracy of the truncated independent product estimator
-- statement:
--   For independent square-integrable real factors with nonzero means and positive product of means, take a positive deterministic scaling factor and 0<epsilon<=1. If the sum of their variances divided by squared means is at most epsilon^2/20, and two measurable nonnegative costs have expectations bounded by positive finite B_f and B_g, then the scaled product is within relative error epsilon and both costs are below their respective cutoffs 16 B_f and 16 B_g with probability at least 13/16. No independence of the costs and estimator is assumed. This combines equation (34) with the truncation step in the proof of Theorem 1.3; source-specific estimator moments and an implementation still need separate proofs.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Theorem 1.3, Section 5.3, equation (34) and truncation, PDF p.21, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

theorem CountingLLL.RandomRAM.product_estimator_cutoff_accuracy {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (a ε : ℝ)
    (ha : 0 < a) (hind : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) ≠ 0)
    (hZ : 0 < ∏ i, ∫ ω, X i ω ∂μ)
    (he0 : 0 < ε) (he1 : ε ≤ 1)
    (hbudget : (∑ i, variance (X i) μ / (∫ ω, X i ω ∂μ) ^ 2) ≤ ε ^ 2 / 20)
    (f g : Ω → ℝ≥0∞) (Bf Bg : ℝ≥0∞)
    (hBf0 : Bf ≠ 0) (hBg0 : Bg ≠ 0) (hBft : Bf ≠ ⊤) (hBgt : Bg ≠ ⊤)
    (hf : Measurable f) (hg : Measurable g)
    (hEf : ∫⁻ ω, f ω ∂μ ≤ Bf) (hEg : ∫⁻ ω, g ω ∂μ ≤ Bg) :
    (13 / 16 : ℝ≥0∞) ≤ μ {ω |
      ((1 - ε) * (a * (∏ i, ∫ ω, X i ω ∂μ)) ≤ a * (∏ i, X i ω) ∧
      a * (∏ i, X i ω) ≤ (1 + ε) * (a * (∏ i, ∫ ω, X i ω ∂μ))) ∧
      f ω < 16 * Bf ∧ g ω < 16 * Bg} := by sorry
