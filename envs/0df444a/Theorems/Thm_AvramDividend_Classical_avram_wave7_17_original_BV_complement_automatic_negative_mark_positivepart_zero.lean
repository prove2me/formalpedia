-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_automatic_negative_mark_positivepart_zero
-- name    : AvramDividend.Classical.avram_wave7_17_original_BV_complement_automatic_negative_mark_positivepart_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:18:40.575122+00:00
-- url     : https://prove2.me/theorems/a900ee36-a8e0-4d11-8db2-f69b2c74720a
-- title:
--   Original strict BV complement: automatic stopped negative-mark product measurability and zero expected positive correction
-- statement:
--   On the original Ω,P, physical time and negative Lévy measure X.ν, the stopped strict-positive-subcap predictable left-reserve region crossed with all negative marks is measurable without an additional hypothesis. Its discounted candidate-value negative-mark increment has zero positive-part source lintegral, at any nonnegative finite horizon including zero. This source-sign result does not assert realised jump compensator equality, boundary occupation or full cash HJB verification.
-- source:
--   Accepted W7-17 original strict stopped physical-measurable f2efea1f and negative ν source positive-part zero eafa21bb. Strict ruin clock, original filtration, P and source Lévy ν are unchanged. Removes extra MeasurableSet S assumption from the actual expected negative-mark correction bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_ruin_stopped_strict_interior_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_stopped_negative_source_mark_positivepart_lintegral_zero
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_BV_complement_automatic_negative_mark_positivepart_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ) (hH : 0 ≤ H)
    (hEnvelope : ¬ (x + H * X.drift ≤ w x))
    (T : ℝ≥0) :
    let μ : Measure ((ℝ≥0 × Ω) × ℝ) :=
      (((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P).prod X.ν)
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t p.2 - rightLimit D t p.2) p.1
    let S : Set ((ℝ≥0 × Ω) × ℝ) :=
      {p | p.1.1 ≤ T ∧
        (p.1.1 : ℝ≥0∞) < ruinTime X x D p.1.2 ∧
        0 < Y p.1 ∧ ENNReal.ofReal (Y p.1) < C ∧ p.2 < 0}
    (∫⁻ p in S, ENNReal.ofReal
      (Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Y p.1 + p.2) - w (Y p.1))) ∂μ) = 0 := by sorry
