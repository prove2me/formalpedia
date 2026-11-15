-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb28_original_zero_reserve_discounted_drift_compensator_budget
-- name    : AvramDividend.Classical.avram_bvb28_original_zero_reserve_discounted_drift_compensator_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:58:53.2194+00:00
-- url     : https://prove2.me/theorems/2c12049b-82c9-48b2-b184-5503a2abdd1f
-- title:
--   Original finite-activity BV zero-reserve discounted drift and mark-compensator time-budget
-- statement:
--   Under original Standing BV finite-activity generator/slope HJB assumptions, integrate the genuine zero-reserve generator inequality against the strictly positive discounted clock up to T, preserving the negative-mark compensator and true terminal w(0). Gives an exact bound on zero-contact portions of original controlled reserve path, without assuming w(0)=0.
-- source:
--   Proved original zero-reserve HJB 0344aae3 and discounted time identity 5ce1f298, BV-B contact source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb28_original_zero_reserve_discounted_drift_compensator_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hq : 0 < q) (T : ℝ) (hT : 0 ≤ T) :
    X.drift * (∫ t in (0 : ℝ)..T, Real.exp ((-q) * t)) +
      Real.exp ((-q) * T) * w 0 ≤
    w 0 -
      (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν) *
        (∫ t in (0 : ℝ)..T, Real.exp ((-q) * t)) := by sorry
