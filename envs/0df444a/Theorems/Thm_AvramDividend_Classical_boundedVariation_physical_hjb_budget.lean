-- Prove2me | Theorems.Thm_AvramDividend_Classical_boundedVariation_physical_hjb_budget
-- name    : AvramDividend.Classical.boundedVariation_physical_hjb_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:41:05.918011+00:00
-- url     : https://prove2.me/theorems/16a44eeb-28c9-4ca2-9770-94c1db514326
-- title:
--   BV HJB budget in physical drift and uncompensated negative jumps
-- statement:
--   A capped HJB supersolution in the bounded-variation Lévy case has an integrable negative-jump increment, physical-drift generator inequality drift*w' + integral(jump increments) <= q*w, and derivative lower bound w'>=1. These are the precise deterministic sign and integrability terms for a stopped finite-variation change-of-variable identity.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_hjb_component_inequalities

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.boundedVariation_physical_hjb_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 < x) (hxC : ENNReal.ofReal x < C) :
    IntegrableOn (fun y : ℝ => w (x + y) - w x) (Iio (0 : ℝ)) X.ν ∧
      X.drift * deriv w x +
          (∫ y in Iio (0 : ℝ), w (x + y) - w x ∂X.ν) ≤ q * w x ∧
      1 ≤ deriv w x := by sorry
