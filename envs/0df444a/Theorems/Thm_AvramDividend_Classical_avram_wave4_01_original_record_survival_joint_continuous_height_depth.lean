-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_survival_joint_continuous_height_depth
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_survival_joint_continuous_height_depth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:25:20.056776+00:00
-- url     : https://prove2.me/theorems/ada5fda3-a81b-4a1e-ba3b-d9766ba3c75d
-- title:
--   Joint continuity of original discounted strict first-record survival in positive height and drawdown depth
-- statement:
--   For a spectrally negative Lévy process with pure infinite variation of small negative jumps, genuine strict upward record time T_h and actual reflected drawdown ruin clock D_a, the expected discounted killed record reward (h,a)↦E[e^{-q T_h}; T_h<D_a] is jointly continuous for h>0 and a>0. It uses the Proved genuine exponential record law G_a(h)=exp(-hκ(a)) and the Proved continuity of the source hazard κ(a)=-log G_a(1); no inferred continuity from separate measurable sections, no Standing, and no fake stochastic axiom.
-- source:
--   Proved source hazard continuity 98caa2b4 and source factor equality 1c71a04d, real exponential composition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_canonical_infinite_jump_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_survival_joint_continuous_height_depth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (∫⁻ ω, if twoSidedExitUpTime X p.1 ω <
                  barrierRuinTime X p.2 ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X p.1 ω).toReal)))
      else 0 ∂P).toReal)
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by sorry
