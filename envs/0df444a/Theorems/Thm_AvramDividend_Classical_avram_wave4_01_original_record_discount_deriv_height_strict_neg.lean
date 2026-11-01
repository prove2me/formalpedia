-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_deriv_height_strict_neg
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_discount_deriv_height_strict_neg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:31:47.976597+00:00
-- url     : https://prove2.me/theorems/3625649a-2a23-4703-9c33-d9b233ce28b7
-- title:
--   Strictly negative height derivative of actual reflected first-record discounted survival
-- statement:
--   The genuine killed first-record discounted mass G_a(h) has strictly negative ordinary derivative in the upward record height h, at every positive a and h, under divergent first absolute small-negative-jump moment and q>0. The Proved exact source height ODE gives G'=-rG, and the new killed/unrestricted root bound yields r>0 while the exact source exponential ensures G>0. No Standing or excursion representation is used.
-- source:
--   Previously Proved source height ODE f2e4c321, genuine first-record log-slope ≥ positive root a5dbcace, original discount exponential 1c71a04d, positive root existence cfe6d3e1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_height_ode

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_01_original_record_discount_deriv_height_strict_neg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ∀ a h : ℝ, 0 < a → 0 < h →
      deriv (fun b : ℝ =>
          (∫⁻ ω, if twoSidedExitUpTime X b ω <
                      barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
          else 0 ∂P).toReal) h < 0 := by sorry
