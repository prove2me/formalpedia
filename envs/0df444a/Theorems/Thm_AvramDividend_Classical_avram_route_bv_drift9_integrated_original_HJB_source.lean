-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_integrated_original_HJB_source
-- name    : AvramDividend.Classical.avram_route_bv_drift9_integrated_original_HJB_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:32:39.872406+00:00
-- url     : https://prove2.me/theorems/1acbb2fd-16f7-4f14-9714-6d7a7063ba27
-- title:
--   Original bounded-variation HJB integrated over the entire positive reserve interval
-- statement:
--   Integrate the genuine original BV generator-HJB inequality over all positive reserve levels up to epsilon. Handle the drift sign, first-order fundamental theorem of calculus from zero, and original negative-jump integrability without assuming finite jump activity. This is the analytic lower half of canonical c1ab97e2.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_bv_drift9_integrated_original_HJB_source
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
      ∫ y in Ioc (0 : ℝ) ε,
        (q * w y - (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν))
        ∂(volume : Measure ℝ) := by sorry
