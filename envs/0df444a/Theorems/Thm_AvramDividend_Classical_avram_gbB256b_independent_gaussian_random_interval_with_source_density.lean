-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB256b_independent_gaussian_random_interval_with_source_density
-- name    : AvramDividend.Classical.avram_gbB256b_independent_gaussian_random_interval_with_source_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T16:03:35.860037+00:00
-- url     : https://prove2.me/theorems/cf2ebe38-0095-45f7-bc3e-f4a94a8ac706
-- title:
--   Independent Gaussian increment enters any past-measurable interval with uniform source-derived small-ball bound
-- statement:
--   Given a Gaussian random variable Z with positive variance and any independent past-measurable random interval centre C, the probability that Z lies in [C,C+epsilon] is bounded by epsilon times the maximal normal density, uniformly in C. The proof integrates the source Gaussian density envelope B253, specialises to intervals, then uses independence to identify the joint law with a product and Fubini to bound the random-centre event. This provides an immediate closed probabilistic building block for the exact original adapted dividend strategy occupation theorem B100, without waiting for additional authoring jobs.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB253_gaussian_pdf_uniform_envelope
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB256b_independent_gaussian_random_interval_with_source_density
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C Z : Ω → ℝ) (hC : Measurable C) (hZ : Measurable Z)
    (mu : ℝ) (v : ℝ≥0) (hv : 0 < v)
    (hLaw : Measure.map Z P = gaussianReal mu v)
    (hInd : IndepFun C Z P)
    (epsilon : ℝ) (hEps : 0 ≤ epsilon) :
    P {ω | C ω ≤ Z ω ∧ Z ω ≤ C ω + epsilon} ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) *
        ENNReal.ofReal epsilon := by sorry
