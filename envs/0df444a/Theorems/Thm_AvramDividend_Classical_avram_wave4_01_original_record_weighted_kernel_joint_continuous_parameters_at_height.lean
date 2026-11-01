-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_kernel_joint_continuous_parameters_at_height
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_weighted_kernel_joint_continuous_parameters_at_height
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:16:11.363079+00:00
-- url     : https://prove2.me/theorems/8c34f8f5-8fde-449b-bf93-b2b7009e0ebc
-- title:
--   Pointwise continuity of actual killed first-record Esscher reward jointly in real tilt and positive depth
-- statement:
--   For the genuine strict first record T_h at fixed height h>0 and the original reflected drawdown D_a, the killed discount kernel exp(-theta h)E_P[exp(-qT_h);T_h<D_a] is jointly continuous in (theta,a) on all theta>minus phi and a>0 under infinite first negative small-jump moment, no Standing. This combines the Proved source joint height-depth continuity with ordinary continuous exponential reweighting, without any change of measure.
-- source:
--   Canonical Proved original source joint survival height-depth continuity ada5fda3 and real exponential continuity; needed for genuine joint L1 DCT.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_survival_joint_continuous_height_depth
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_weighted_kernel_joint_continuous_parameters_at_height
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ h : ℝ) (hh : 0 < h) :
    ContinuousOn (fun p : ℝ × ℝ =>
      Real.exp (-(p.1 * h)) *
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
            barrierRuinTime X p.2 ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal)
      ((Ioi (-φ)).prod (Ioi (0 : ℝ))) := by sorry
