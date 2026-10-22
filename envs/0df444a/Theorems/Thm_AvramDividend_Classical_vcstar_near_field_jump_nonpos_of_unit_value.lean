-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_near_field_jump_nonpos_of_unit_value
-- name    : AvramDividend.Classical.vcstar_near_field_jump_nonpos_of_unit_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:35:51.362026+00:00
-- url     : https://prove2.me/theorems/f3b81d2e-7bc7-4b81-97d0-758596a33b9c
-- title:
--   Nonlocal dividend generator inequality above the cap with a unit value floor
-- statement:
--   For reserve x strictly above the canonical dividend cap a, assume global monotonicity and a left affine-majorant of the barrier value, together with v(x)≥1 and c≤qv(x). Every large negative jump has nonpositive increment. A compensated small jump that crosses below zero also has nonpositive increment because v(x)≥1>−y. All other small jumps are controlled by the affine-majorant or cancel on the right affine branch. Consequently the entire nonlocal jump integral is nonpositive, generator-domain integrability holds and Γv(x)−qv(x)≤0, including possible x<1.

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrier_generatorIntegrand_zero_small_negative_jump_above
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_above_eq_drift_add_jump
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_near_field_jump_nonpos_of_unit_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hmono : Monotone (vcstar W))
    (hchord : ∀ z : ℝ, 0 ≤ z → z ≤ (cstar W).toReal →
      vcstar W z ≤
        z - (cstar W).toReal + vcstar W (cstar W).toReal)
    (x : ℝ) (hx : (cstar W).toReal < x)
    (hunit : 1 ≤ vcstar W x)
    (hbound : X.c ≤ q * vcstar W x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x - q * vcstar W x ≤ 0 := by sorry
