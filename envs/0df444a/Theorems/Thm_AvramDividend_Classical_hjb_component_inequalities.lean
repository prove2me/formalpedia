-- Prove2me | Theorems.Thm_AvramDividend_Classical_hjb_component_inequalities
-- name    : AvramDividend.Classical.hjb_component_inequalities
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:10:59.377977+00:00
-- url     : https://prove2.me/theorems/6a37aabf-2ec1-42a8-aae8-07cdaa13bc87
-- title:
--   Component inequalities implied by the dividend HJB maximum equation
-- statement:
--   At every positive state below the cap, equation (5.8) implies generator integrability, the nonpositive discounted-generator drift Γw−qw≤0, and the marginal-dividend inequality w′≥1. This packages the two component inequalities of max{Γw−qw,1−w′}=0 for the verification proof.
-- source:
--   Avram, Palmowski and Pistorius (2007), Equation (5.8), p. 17, used in Proposition 4(i). Immediate order consequences of the maximum equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.hjb_component_inequalities
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (y : ℝ) (hy : 0 < y) (hyC : ENNReal.ofReal y < C) :
    X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0 ∧
      1 ≤ deriv w y := by sorry
