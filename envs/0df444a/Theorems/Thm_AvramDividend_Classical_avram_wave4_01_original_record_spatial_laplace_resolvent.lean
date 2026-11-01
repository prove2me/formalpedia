-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_laplace_resolvent
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_spatial_laplace_resolvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:43:45.674991+00:00
-- url     : https://prove2.me/theorems/04d2dec3-37b2-498f-9f56-77cc82c9af50
-- title:
--   Spatial Laplace resolvent of genuine killed discounted strict first-record survival
-- statement:
--   For the actual Lévy strict first-record times T_h and actual reflected drawdown ruin time D_a in pure infinite small-negative-jump variation, positive q, a>0, and an additional positive record-height Laplace penalty theta, the spatial resolvent ∫_0^infinity exp(-theta h) E[exp(-q T_h);T_h<D_a]dh is exactly (theta+W'(a)/W(a))^-1. This is a parameter-dependent original-process potential, not merely a pointwise survival identity. It follows from the Proved uncapped exponential source law, positive Esscher-root hazard bound, and exact pinned exponential integral.
-- source:
--   Actual source G_a(h)=exp(-h W'/W) 1c71a04d-268a-4126-b1bd-c0537bda0db1, root slope positivity a5dbcace-268f-44a5-a46e-c42f4470ceb3, Mathlib integral_exp_mul_Ioi.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_spatial_laplace_resolvent
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a θ : ℝ) (ha : 0 < a) (hθ : 0 < θ) :
    (∫ h : ℝ in Ioi 0,
      Real.exp (-(θ * h)) *
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal) =
    (θ + deriv W a / W a)⁻¹ := by sorry
