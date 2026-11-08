-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_spatial_jump_loss_upper
-- name    : AvramDividend.Classical.avram_route_bv_drift9_original_spatial_jump_loss_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:32:40.889142+00:00
-- url     : https://prove2.me/theorems/dbf43484-d48a-4f4c-b756-51471e6b4d5d
-- title:
--   Original negative-jump spatial loss bounded by truncated Levy first moments
-- statement:
--   For each original negative jump z, spatial integration of w(y)-w(y+z) over (0,epsilon] is bounded by min(epsilon,-z) times w(epsilon), using the zero-extension at negative surplus and monotone C1 candidate. Tonelli converts this to the genuine original Lévy measure bound; q-times spatial value contributes q epsilon w(epsilon). No finite activity assumption. This is the independent analytic upper half of canonical c1ab97e2.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_bv_drift9_original_spatial_jump_loss_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hwzero : w 0 = 0)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C) (hε1 : ε ≤ 1) :
    (∫ y in Ioc (0 : ℝ) ε,
      (q * w y - (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν))
      ∂(volume : Measure ℝ)) ≤
    (q * ε + (∫ z in Iio (0 : ℝ), min ε (-z) ∂X.ν)) * w ε := by sorry
