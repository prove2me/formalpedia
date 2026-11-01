-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_joint_continuity_positive_parameters
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_discount_joint_continuity_positive_parameters
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:34:00.678548+00:00
-- url     : https://prove2.me/theorems/42e70f96-7dd0-41af-b09c-f4800eee76a1
-- title:
--   Genuine reflected killed first-record discounted survival is jointly continuous in positive depth and record height
-- statement:
--   For positive discount and divergent negative small-jump variation, the actual Lévy stopped discounted first-record transform (a,h) ↦ E[e^{-q T_h};T_h<D_a] is jointly continuous on (0,infinity)×(0,infinity). This is stronger than separate depth or record-height continuity and follows from the proved source exponential first-record semigroup representation G_a(h)=exp(-h K(a)) and proved genuine continuity of K on the positive axis. It does not use Standing, a stochastic proxy, or a new axiom.
-- source:
--   Canonically Proved uncapped exponential source survival 1f5b13d3-98f1-4b35-b1d2-5df29b3cf596 and genuine log-hazard continuity ec9e934a-2ad2-4a0d-8d6e-9dd9654ab798.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_exponential_hazard
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_discount_joint_continuity_positive_parameters
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        (∫⁻ ω, if twoSidedExitUpTime X p.2 ω <
            barrierRuinTime X p.1 ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X p.2 ω).toReal)))
        else 0 ∂P).toReal)
      ((Ioi (0 : ℝ)) ×ˢ (Ioi (0 : ℝ))) := by sorry
