-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_generator_gradient_hjb_subsolution_inequality
-- name    : AvramDividend.Classical.bv_generator_gradient_hjb_subsolution_inequality
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:36:55.704991+00:00
-- url     : https://prove2.me/theorems/a3ef26d1-8bae-4b38-a6da-c5455607a9f6
-- title:
--   Bounded-variation generator and gradient conditions imply the HJB subsolution inequality
-- statement:
--   The bounded-variation verification core assumes the generator contribution minus discount is nonpositive and the derivative is at least one on positive interior reserves. These two bounds directly imply the corresponding Hamilton-Jacobi-Bellman maximum is nonpositive. Equality of the maximum is unnecessary for verification of a subsolution.

import Mathlib.Data.Real.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.bv_generator_gradient_hjb_subsolution_inequality
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      max (X.generator w y - q * w y) (1 - deriv w y) ≤ 0 := by sorry
