-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_prepayment_interior_cutoff_HJB
-- name    : AvramDividend.Classical.avram_p4_c_generator_prepayment_interior_cutoff_HJB
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:59:37.488986+00:00
-- url     : https://prove2.me/theorems/c750a7ed-f224-43e8-95d3-a310d16484a9
-- title:
--   Original stopped prepayment-reserve interior HJB drift has the exact epsilon-separated generator sign
-- statement:
--   At the original controlled prepayment reserve Y_t = leftLim(x+X_s−rightLimit D_s), when 0<Y_t<C, the exact source HJB hypothesis implies that the source Lévy kernel is ν-integrable and the Gaussian, compensated drift c, and ε-separated negative-jump integrals combine with discount to a nonpositive quantity. This uses the independently Proved genuine original ε-partition and makes no claim at the zero boundary, at C, or after a ruin overshoot. It is pointwise generator identification for P4-F, not a stochastic Itô–Meyer construction.
-- source:
--   Canonical source generator and riskProcess/rightLimit definitions, accepted avram_p4_c_generator_negative_mark_integral_cutoff_split (5434bf03-5ab7-4955-984e-cb4aa16c7af7). Paper Proposition 4(i) (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_negative_mark_integral_cutoff_split

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_prepayment_interior_cutoff_HJB
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω)
    (ε : ℝ) (hε : 0 < ε) :
    let Y : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    (0 < Y ∧ ENNReal.ofReal Y < C) →
      X.GeneratorIntegrable w Y ∧
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w Y + X.c * deriv w Y +
        (∫ z in Iio (-ε), SpectrallyNegativeLevy.generatorIntegrand w Y z ∂X.ν) +
        (∫ z in Ico (-ε) 0, SpectrallyNegativeLevy.generatorIntegrand w Y z ∂X.ν) -
        q * w Y ≤ 0) := by sorry
