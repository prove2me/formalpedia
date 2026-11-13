-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_source_accuracy_exact_sample_count
-- name    : CountingLLL.RandomRAM.source_accuracy_exact_sample_count
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:28:23.918198+00:00
-- url     : https://prove2.me/theorems/9b9fbb68-26c0-40ed-81c8-a201f5c80c3a
-- title:
--   Counting accuracy with the source sample count
-- statement:
--   Under Condition 1.1 and the stated marginal mean and variance bounds, set the positive integer sample count to the exact ceiling used in Section 5.3, L=ceil(8m/((D+1)^2 epsilon^2)). For a nonempty finite constraint index set, a positive deterministic scaling factor, independent square-integrable marginal factors, and two measurable costs with positive finite expectation bounds, the scaled product is within relative error epsilon and both costs lie below 16 times their respective expected-cost bounds with probability at least 13/16. The specific randomized marginal algorithms and their moment and cost bounds remain hypotheses.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Theorem 1.3, Section 5.3, equation (34) and truncation, PDF pp.20-21, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

theorem CountingLLL.RandomRAM.source_accuracy_exact_sample_count {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (r : ι → ℝ)
    (a p D ε : ℝ) (L : ℕ)
    (hm : 0 < Fintype.card ι)
    (hLspec : L = ⌈8 * (Fintype.card ι : ℝ) / ((D + 1)^2 * ε^2)⌉₊)
    (ha : 0 < a) (hp : 0 ≤ p) (hD : 1 ≤ D) (he : 0 < ε) (he1 : ε ≤ 1)
    (hcondition : 4 * Real.exp 1 * p * (D + 1) ^ 2 ≤ 1)
    (hr0 : ∀ i, 0 ≤ r i) (hr : ∀ i, r i ≤ (6 / 5) * p)
    (hind : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 1 - r i)
    (hvar : ∀ i, variance (X i) μ ≤ 3 * p / (L : ℝ))
    (f g : Ω → ℝ≥0∞) (Bf Bg : ℝ≥0∞)
    (hBf0 : Bf ≠ 0) (hBg0 : Bg ≠ 0) (hBft : Bf ≠ ⊤) (hBgt : Bg ≠ ⊤)
    (hf : Measurable f) (hg : Measurable g)
    (hEf : ∫⁻ ω, f ω ∂μ ≤ Bf) (hEg : ∫⁻ ω, g ω ∂μ ≤ Bg) :
    (13 / 16 : ℝ≥0∞) ≤ μ {ω |
      ((1 - ε) * (a * (∏ i, (1 - r i))) ≤ a * (∏ i, X i ω) ∧
      a * (∏ i, X i ω) ≤ (1 + ε) * (a * (∏ i, (1 - r i)))) ∧
      f ω < 16 * Bf ∧ g ω < 16 * Bg} := by sorry
