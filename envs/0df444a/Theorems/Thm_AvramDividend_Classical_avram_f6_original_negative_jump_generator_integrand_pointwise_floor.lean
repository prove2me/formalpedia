-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_negative_jump_generator_integrand_pointwise_floor
-- name    : AvramDividend.Classical.avram_f6_original_negative_jump_generator_integrand_pointwise_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:45:40.801184+00:00
-- url     : https://prove2.me/theorems/4958a89b-c177-471d-801f-702d9597fb0c
-- title:
--   Original negative-jump HJB generator integrand bounded below by minus candidate w
-- statement:
--   For actual original Lévy generatorIntegrand w y z, z<0, if w≥0 and deriv w y≥0 then the compensated integrand is ≥−w y, because the negative-jump linear compensation is nonnegative.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_negative_jump_generator_integrand_pointwise_floor
    (w : ℝ → ℝ) (y z : ℝ)
    (hwpos : ∀ u : ℝ, 0 ≤ w u)
    (hd : 0 ≤ deriv w y) (hz : z < 0) :
    -w y ≤ SpectrallyNegativeLevy.generatorIntegrand w y z := by sorry
