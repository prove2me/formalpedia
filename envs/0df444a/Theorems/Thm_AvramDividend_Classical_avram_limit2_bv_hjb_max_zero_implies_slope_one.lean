-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_hjb_max_zero_implies_slope_one
-- name    : AvramDividend.Classical.avram_limit2_bv_hjb_max_zero_implies_slope_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:28:22.240212+00:00
-- url     : https://prove2.me/theorems/860711a8-1822-4401-a4c4-7b18f9d78ba0
-- title:
--   Original BV HJB maximum identity implies slope one for perpetual-cash passage
-- statement:
--   For the exact original bounded-variation HJB condition used by admissible_cap_dividendValue_le_bounded_variation, the maximum of the drift-generator term and the dividend-gradient complement being zero forces 1 - deriv w y <= 0 at each positive reserve strictly inside the cap. Consequently the original BV slope-one hypothesis used by the accepted real-perpetual cash adapter follows without a second assumption.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_bv_hjb_max_zero_implies_slope_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y := by sorry
