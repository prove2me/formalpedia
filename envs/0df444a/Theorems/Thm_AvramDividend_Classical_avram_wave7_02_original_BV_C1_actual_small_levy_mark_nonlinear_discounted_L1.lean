-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_actual_small_levy_mark_nonlinear_discounted_L1
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_C1_actual_small_levy_mark_nonlinear_discounted_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:27:43.095713+00:00
-- url     : https://prove2.me/theorems/f827dbd6-73d2-40d6-893b-ceb2cacf60ae
-- title:
--   Original bounded variation Levy C1 discounted nonlinear small negative mark kernel is absolutely ν-integrable
-- statement:
--   For original source X with BV first negative Levy jump moment, the discounted C1 nonlinear difference w(left reserve+z)-w(left reserve), evaluated at actual controlled predictable left surplus inside positive strip, is absolutely integrable with respect to the original physical negative Levy measure on (-a/2,0). Use local C1 Lipschitz constant, a<=2 and original BV moment theorem; mark strong measurability is stated independently. This is a true Levy integrability bridge, with neither C2 nor a substitute source.
-- source:
--   Actual BV small-negative first moment bv_small_negative_first_moment_integrable (Proved) and W7-02 physical source mark pointwise discounted variation estimate e6763634 (Proved candidate 22366).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_predictable_small_mark_discounted_L1_by_source_variation
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_C1_actual_small_levy_mark_nonlinear_discounted_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (a b L : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hL : 0 ≤ L)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (ω : Ω) (t : ℝ≥0)
    (hBand : Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t ∈ Icc a b)
    (hMeas : AEStronglyMeasurable (fun z : ℝ =>
      Real.exp (-(q * (t : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t + z) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t)))
      (X.ν.restrict (Ioo (-a / 2) 0))) :
    IntegrableOn (fun z : ℝ =>
      Real.exp (-(q * (t : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t + z) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) t)))
      (Ioo (-a / 2) 0) X.ν := by sorry
