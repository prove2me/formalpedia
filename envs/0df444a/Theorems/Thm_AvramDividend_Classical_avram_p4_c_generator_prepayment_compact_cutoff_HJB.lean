-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_prepayment_compact_cutoff_HJB
-- name    : AvramDividend.Classical.avram_p4_c_generator_prepayment_compact_cutoff_HJB
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:00:57.558787+00:00
-- url     : https://prove2.me/theorems/dac8be18-f7c6-4c1a-9000-1df895d44834
-- title:
--   Original controlled left-limit HJB sign with epsilon physical drift and compact large-jump integral
-- statement:
--   At an actual original prepayment controlled reserve left limit Y and strict 0<Y<C, source HJB and GeneratorIntegrable imply the nonpositive discount-generator residual expressed with Gaussian correction, epsilon-physical drift, one uncorrected large-jump integral over z<-epsilon and one compensated small remainder over -epsilon≤z<0. No assertion is made at boundary, after ruin overshoot, or about stochastic compensation.
-- source:
--   original source HJB, controlled left limit, P4-C original_epsilon_drift_compact

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_prepayment_compact_cutoff_HJB
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    let Y : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    (0 < Y ∧ ENNReal.ofReal Y < C) →
      X.σ ^ 2 / 2 * iteratedDeriv 2 w Y +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w Y +
        (∫ z in Iio (-ε), w (Y + z) - w Y ∂X.ν) +
        (∫ z in Ico (-ε) 0,
          SpectrallyNegativeLevy.generatorIntegrand w Y z ∂X.ν) -
        q * w Y ≤ 0 := by sorry
