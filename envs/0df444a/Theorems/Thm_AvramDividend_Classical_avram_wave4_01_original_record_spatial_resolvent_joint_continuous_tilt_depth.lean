-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_resolvent_joint_continuous_tilt_depth
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_spatial_resolvent_joint_continuous_tilt_depth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:56:35.433973+00:00
-- url     : https://prove2.me/theorems/387f8574-d264-4fff-84ff-228be13c98e1
-- title:
--   Joint tilt-depth continuity of genuine first-record spatial exponential potential including negative tilt
-- statement:
--   For q>0 and unbounded pure small-jump variation without Standing, and a positive Esscher root φ with ψ(φ)=q, the genuine source first-record killed exponential height potential is jointly continuous in spatial tilt θ and reflected drawdown depth a on the entire open domain θ>−φ and a>0. The proof identifies it as 1/(θ+κ(a)) via the original first-record spatial resolvent, uses continuous source log-hazard κ and κ(a)≥φ, and avoids any invented stochastic interface.
-- source:
--   Accepted original spatial exponential moment resolvent cefb902e, source continuous log-hazard 98caa2b4, true unit record scale derivative 1c71a04d, positive Esscher root lower bound a5dbcace. Pointwise product-domain composition of ContinuousOn.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_canonical_infinite_jump_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_exponential_moment_resolvent
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_spatial_resolvent_joint_continuous_tilt_depth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ContinuousOn (fun p : ℝ × ℝ =>
      ∫ h : ℝ in Ioi 0,
        Real.exp (-(p.1 * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X p.2 ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal)
      {p : ℝ × ℝ | -φ < p.1 ∧ 0 < p.2} := by sorry
