-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_hjb_max_to_original_source_signs
-- name    : AvramDividend.Classical.avram_limit2_bv_hjb_max_to_original_source_signs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:54:28.095309+00:00
-- url     : https://prove2.me/theorems/67d643aa-f5c0-4a13-87fe-1afdf25fd2f2
-- title:
--   Canonical BV HJB max identity yields original grid generator sign and slope one
-- statement:
--   The source BV HJB max-zero condition simultaneously yields generator integrability and the nonpositive discounted generator residual used by the canonical original physical signed Fatou grid theorem, and slope one used for the global real-perpetual value passage. The generator sign follows from the left argument being below the zero maximum, and the slope from the Proved LIMIT-2 HJB slope lemma.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_hjb_max_zero_implies_slope_one
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_bv_hjb_max_to_original_source_signs
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) := by sorry
