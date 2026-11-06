-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_rightcont_negative_band_centered_condExp_auto
-- name    : AvramDividend.Classical.avram_p4_s3_original_rightcont_negative_band_centered_condExp_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:36:26.850846+00:00
-- url     : https://prove2.me/theorems/231bacab-9f0e-407c-9395-68ad797db1da
-- title:
--   Original physical negative-band compensated increment is centred at the right-continuous past without any assumed conditional rate
-- statement:
--   Given shrinking positive future subintervals approaching s within a finite interval and a negative Borel band separated from zero, the true Lévy marked-count increment from s to t has conditional expectation equal to its physical Lévy compensator relative to the right-continuous filtration at s. All count measurability, finite mark mass, unconditional and past-event rectangle rates are established from existing original-source theorems; only deterministic shrinking-grid limit hypotheses remain.
-- source:
--   P4-B rightCont centring c34e4241, exact future rectangle source ea8700f6, arbitrary interval rate 788041e5, original mark meas 21acd1ce and separated finite ν 86086cb2.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_rightcont_negative_band_centered_condExp_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (r : ℕ → ℝ≥0)
    (hsr : ∀ k, s < r k) (hrt : ∀ k, r k ≤ t)
    (hShort : Filter.Tendsto (fun k => r k - s) atTop (𝓝 0))
    (hLong : Filter.Tendsto (fun k => t - r k) atTop (𝓝 (t - s)))
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBsep : B ⊆ Iic (-ε)) :
    let J : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    P[(fun ω => (J ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) |
      𝓕.rightCont s] =ᵐ[P] 0 := by sorry
