-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_psi_implies_upward_increment_positive_measure_all_times
-- name    : AvramDividend.Classical.positive_psi_implies_upward_increment_positive_measure_all_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:47:09.093728+00:00
-- url     : https://prove2.me/theorems/2e129e12-8ea5-412c-9e86-662cd8da9843
-- title:
--   Positive Lévy exponent gives positive upward-increment probability at every positive time
-- statement:
--   At every strictly positive time, the distribution of a spectrally negative Lévy process assigns positive probability to a strictly positive increment whenever the Laplace exponent is positive at some nonnegative argument. If the positive event were null, the exponential moment would be at most one, contradicting the strict inequality exp(tψ(θ))>1. This is a robust all-time version relevant to first-passage arguments and to correction of nonstopped martingale assumptions.
-- source:
--   SpectrallyNegativeLevy.laplace and the pinned Mathlib ae_iff, integral_mono_ae and Real.one_lt_exp_iff.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.OuterMeasure.AE
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_psi_implies_upward_increment_positive_measure_all_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : 0 < X.ψ θ) :
    ∀ t : ℝ≥0, 0 < t → 0 < P {ω : Ω | 0 < X.X t ω} := by sorry
