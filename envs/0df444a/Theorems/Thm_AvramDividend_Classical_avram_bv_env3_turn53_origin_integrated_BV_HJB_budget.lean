-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn53_origin_integrated_BV_HJB_budget
-- name    : AvramDividend.Classical.avram_bv_env3_turn53_origin_integrated_BV_HJB_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T10:14:56.142668+00:00
-- url     : https://prove2.me/theorems/c1ab97e2-d8bb-413d-bfa5-481826595a16
-- title:
--   Original BV HJB integrated near-origin jump-loss and positive-drift budget
-- statement:
--   Assuming the zero HJB boundary w(0)=0, integrate the original BV generator inequality over [delta,epsilon] and send delta down to zero. Positive drift contributes drift*w(epsilon). The discounted value contributes at most q*epsilon*w(epsilon). Tonelli and the exact one-dimensional translation identity bound the integrated negative-jump loss by w(epsilon) times the actual truncated Lévy first moment ∫_{z<0} min(epsilon,-z) ν(dz). The result is an exact original-generator near-origin coercive inequality, with no stopped process or dividend proxy.
-- source:
--   Proved boundedVariation_generator_physical_drift_representation c8ba98f0 and original C1/continuity gradient inputs; Tonelli under nonnegative loss and bounded-variation small-jump first moment; original ν, no altered law or process.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn53_origin_integrated_BV_HJB_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hwzero : w 0 = 0)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C) (hε1 : ε ≤ 1) :
    X.drift * w ε ≤
      (q * ε + (∫ z in Iio (0 : ℝ), min ε (-z) ∂X.ν)) * w ε := by sorry
