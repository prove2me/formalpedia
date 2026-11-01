-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_resolvent_continuous_depth_negative_tilt
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_spatial_resolvent_continuous_depth_negative_tilt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:49:32.932148+00:00
-- url     : https://prove2.me/theorems/4413c284-9dcd-4cd3-b4c3-006587f889ff
-- title:
--   Continuous drawdown-depth dependence of the true first-record exponential height potential even at negative spatial tilt
-- statement:
--   For every real θ>-φ where ψ(φ)=q and φ>0, the genuine source discounted first-record spatial potential ∫_{h>0}exp(-θ h)E[exp(-qT_h); T_h<D_a]dh depends continuously on positive reflected drawdown depth a, even when θ<0 induces exponential growth in height. The exact source hazard is continuous and ≥φ, so the previously proved authentic height resolvent is a continuous reciprocal of a strictly positive denominator; no unjustified almost-everywhere or Laplace-only C1 inference.
-- source:
--   Source log hazard continuous 98caa2b4, exact height-one G=exp(-W'/W) 1c71a04d, source negative-tilt potential cefb902e, slope bound a5dbcace; pinned ContinuousOn.div.

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

theorem AvramDividend.Classical.avram_wave4_01_original_record_spatial_resolvent_continuous_depth_negative_tilt
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (θ : ℝ) (hθ : -φ < θ) :
    ContinuousOn (fun a : ℝ =>
      ∫ h : ℝ in Ioi 0,
        Real.exp (-(θ * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal) (Ioi 0) := by sorry
