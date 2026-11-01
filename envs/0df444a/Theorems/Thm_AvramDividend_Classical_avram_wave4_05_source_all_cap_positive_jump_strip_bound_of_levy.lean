-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_all_cap_positive_jump_strip_bound_of_levy
-- name    : AvramDividend.Classical.avram_wave4_05_source_all_cap_positive_jump_strip_bound_of_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:43:57.112457+00:00
-- url     : https://prove2.me/theorems/783729ce-c7ad-4cc2-990f-caf6b626e656
-- title:
--   All-cap finite Levy ruin strip and uniform compensated positive jump bound from source assumptions
-- statement:
--   For any strict upper reserve and any source optimal cap, zero included, original Levy negative-jump intensity is finite on the strict ruin-crossing small-jump band, and the positive part of the compensated generator integrand is bounded pointwise by the barrier shortfall. No independently imposed Levy moment premise.
-- source:
--   levy_negative_mass_away_from_zero_finite and accepted original all-cap generator jump positive-part identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_all_cap_positive_jump_strip_bound_of_levy {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) (hx : (cstar W).toReal < x) : X.ν (Ioo (-1 : ℝ) (-x)) < ⊤ ∧ ∀ y : ℝ, y < 0 → max 0 (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y) ≤ max 0 (1 - vcstar W x) := by sorry
