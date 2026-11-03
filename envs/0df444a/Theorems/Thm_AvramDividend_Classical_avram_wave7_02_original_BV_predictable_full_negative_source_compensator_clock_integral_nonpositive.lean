-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_full_negative_source_compensator_clock_integral_nonpositive
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_predictable_full_negative_source_compensator_clock_integral_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:50:19.373592+00:00
-- url     : https://prove2.me/theorems/783c30f7-34d7-4883-ba9f-f9d49116a651
-- title:
--   Actual BV predictable clock integral of the full discounted negative Levy compensator across ruin overshoots
-- statement:
--   On a measurable space-time stopped interior region of the original source filtration, the negative Levy compensation ν-integral of w at the original predictable left reserve is nonpositive after discount when explicitly integrable. Includes overshoot marks and uses no replacement measure. The identity equating realised jumps and predictable compensation is a separate stochastic task.
-- source:
--   Proved W7-02 original BV negative ν-integral sign theorem 10b2b885 and original predictable-space-time integral sign transfer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_full_negative_mark_compensator_integral_ruin_overshoot_nonpositive
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_predictable_full_negative_source_compensator_clock_integral_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E,
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (hMarkInt : ∀ p ∈ E,
      IntegrableOn (fun z : ℝ =>
        w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
        w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1))
        (Iio 0) X.ν)
    (hClockInt : IntegrableOn
      (fun p : ℝ≥0 × Ω =>
        Real.exp (-(q * (p.1 : ℝ))) *
          (∫ z in Iio (0 : ℝ),
            w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
            w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν))
      E μ) :
    (∫ p in E,
      Real.exp (-(q * (p.1 : ℝ))) *
        (∫ z in Iio (0 : ℝ),
          w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 + z) -
          w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) ∂X.ν)
       ∂μ) ≤ 0 := by sorry
