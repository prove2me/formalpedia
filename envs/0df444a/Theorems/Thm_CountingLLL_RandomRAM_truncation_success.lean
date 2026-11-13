-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_truncation_success
-- name    : CountingLLL.RandomRAM.truncation_success
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:06:44.920202+00:00
-- url     : https://prove2.me/theorems/5ded513e-d27b-465d-b9cc-07d0b8a6e84c
-- title:
--   Two cost cutoffs preserve randomized counting accuracy
-- statement:
--   Let G be an event of probability at least 15/16, and let f and g be measurable nonnegative extended-real costs, each with expectation at most one. Then the event that G occurs and both costs are below 16 has probability at least 13/16. Thus two separate cost cutoffs can make a randomized estimator worst-case bounded while preserving probability greater than 3/4; independence of the costs and the success event is not needed. The costs here are normalized by their respective expected-cost bounds.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Theorem 1.3, Section 5.3, PDF p.21, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem CountingLLL.RandomRAM.truncation_success {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (G : Set Ω) (f g : Ω → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hEf : ∫⁻ ω, f ω ∂μ ≤ 1) (hEg : ∫⁻ ω, g ω ∂μ ≤ 1)
    (hgood : (15 / 16 : ℝ≥0∞) ≤ μ G) :
    (13 / 16 : ℝ≥0∞) ≤ μ {ω | ω ∈ G ∧ f ω < 16 ∧ g ω < 16} := by sorry
