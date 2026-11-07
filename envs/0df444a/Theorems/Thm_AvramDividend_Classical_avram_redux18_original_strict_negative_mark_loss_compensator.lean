-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_original_strict_negative_mark_loss_compensator
-- name    : AvramDividend.Classical.avram_redux18_original_strict_negative_mark_loss_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:37:46.241351+00:00
-- url     : https://prove2.me/theorems/db9a5093-e3c1-4fef-ad64-1d83249c80e2
-- title:
--   Original strict negative-band exponential mark loss has exact Levy compensator
-- statement:
--   The genuine original spectrally negative Levy process satisfies an exact Campbell identity for the strict negative jump cutoff y < -epsilon and the mark-loss weight 1-exp(y): the expected intrinsic marked loss equals horizon T times the original Levy measure integral on the same strict band. This keeps the original process, positive and zero horizons, and the exact strict cutoff of the canonical marked-Laplace theorem.
-- source:
--   Specialise the Proved original separated negative-band weighted compensator to the measurable strict-cutoff indicator of ENNReal.ofReal(1-exp(y)), use Iio(-epsilon) subset Iic(-epsilon), then rewrite the outer weighted integral using the pinned lintegral_indicator theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux18_original_negative_band_weighted_levy_compensator
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_redux18_original_strict_negative_mark_loss_compensator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (ε : ℝ) (hε : 0 < ε) :
    let φ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (1 - Real.exp y)
    let B : Set ℝ := Iio (-ε)
    (∫⁻ ω, ∫⁻ p in (Ioc 0 T ×ˢ (univ : Set ℝ)),
      (B.indicator φ) p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P) =
      (T : ℝ≥0∞) * (∫⁻ y in B, φ y ∂X.ν) := by sorry
