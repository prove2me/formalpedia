-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_tendsto_infinity_zero_depth
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_hazard_tendsto_infinity_zero_depth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:00:07.375882+00:00
-- url     : https://prove2.me/theorems/800cd189-f02c-439e-8919-17259775ab86
-- title:
--   Genuine reflected strict-record hazard diverges as drawdown depth decreases to zero
-- statement:
--   For the actual strict upward first-record time and actual reflected drawdown ruin clock under divergent absolute negative small-jump moment, the positive-depth hazard K(a)=-log E[e^{-q T_1}; T_1<D_a] diverges to +infinity as a approaches zero from above. The proved source chord inequality bounds K(a) below by [log W(1)-log W(a)]/(1-a). In unbounded variation W(0)=0 and W is continuous and strictly positive on the positive axis, so log W(a) goes to minus infinity as a decreases to zero; the chord diverges to infinity. This is a genuine boundary stochastic hazard statement with no Standing, no excursion surrogate and no stochastic axiom.
-- source:
--   Source chord lower bound 62d306c1-788a-41d1-935d-7e3d45ccf130; zero origin c1b8958a-41fd-444e-893e-cf03e591b93e; global continuity 9e68affb-d2da-4e61-b6fc-dd672e06e3cb; positive scale; Mathlib log near-zero asymptotic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_chord_lower_bound
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_hazard_tendsto_infinity_zero_depth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    Tendsto
      (fun a : ℝ => -Real.log
        ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
          else 0 ∂P).toReal))
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry
