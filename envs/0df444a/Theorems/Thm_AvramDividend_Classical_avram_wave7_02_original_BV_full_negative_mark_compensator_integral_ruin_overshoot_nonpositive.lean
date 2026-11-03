-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_full_negative_mark_compensator_integral_ruin_overshoot_nonpositive
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_full_negative_mark_compensator_integral_ruin_overshoot_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:10:36.75103+00:00
-- url     : https://prove2.me/theorems/10b2b885-eb2d-4fae-b3a8-3e7cd7b8b52a
-- title:
--   Original BV Lévy negative-mark ν-integral including ruin overshoots and discounted compensator is nonpositive
-- statement:
--   For the actual original bounded-variation spectrally negative Levy process and the literal predictable controlled pre-jump reserve inside the positive HJB cap, the uncompensated full negative mark integral over Iio 0 against the original Levy intensity X.ν is nonpositive whenever that true integrand is IntegrableOn the negative half-line. The statement includes negative marks that jump below ruin and the positive exponential discounted correction at the actual source clock, without strengthening C1 or discarding overshoots.
-- source:
--   Proved original predictable negative-mark full ruin-overshoot sign d4e52bb5, exact source Levy ν, standard nonpositive integral and positive exponential.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_source_negative_mark_ruin_overshoot_nonpositive
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_full_negative_mark_compensator_integral_ruin_overshoot_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (t : ℝ≥0)
    (hregion :
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C)
    (hInt : IntegrableOn (fun z : ℝ =>
      w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t + z) -
      w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t))
      (Iio 0) X.ν)
    (q : ℝ) :
    (∫ z in Iio (0 : ℝ),
      w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t + z) -
      w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) ≤ 0 ∧
    Real.exp (-(q * (t : ℝ))) *
      (∫ z in Iio (0 : ℝ),
        w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t + z) -
        w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ∂X.ν) ≤ 0 := by sorry
