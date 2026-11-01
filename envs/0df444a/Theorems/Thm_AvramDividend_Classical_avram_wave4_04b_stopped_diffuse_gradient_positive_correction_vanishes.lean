-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_stopped_diffuse_gradient_positive_correction_vanishes
-- name    : AvramDividend.Classical.avram_wave4_04b_stopped_diffuse_gradient_positive_correction_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:14:50.82+00:00
-- url     : https://prove2.me/theorems/3debb0eb-03ff-4303-b888-fec1bcb6e738
-- title:
--   The positive part of the stopped signed continuous Stieltjes dividend correction vanishes for every atomless control measure
-- statement:
--   For the genuine Lévy-driven controlled reserve and any atomless Stieltjes time measure, including a pathwise singular-continuous dividend remainder, the positive-part lintegral of the precisely signed continuous Itô–Meyer dividend correction exp(-qt)(1-deriv w(A_t)) vanishes over the stopped finite-horizon window. This follows from the HJB gradient only at paid strict-interior reserve times and retains the actual discounted time geometry. The statement neither assumes absolute continuity nor claims a source-X stochastic semimartingale decomposition.
-- source:
--   Canonical paymentTimes measurable, strict interior gradient, exact real/NNReal time conversion and a measure-theoretic indicator lintegral argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_stopped_diffuse_gradient_positive_correction_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (q : ℝ)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (hloc : ∀ t : ℝ≥0, t ≤ T → (t : ℝ) ∈ paymentTimes τ →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C) :
    (∫⁻ s in paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal
        (Real.exp (-q * s) *
          (1 - deriv w (riskProcess X x D s.toNNReal ω))) ∂ν) = 0 := by sorry
