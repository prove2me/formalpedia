-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_exponential_moment_resolvent
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_spatial_exponential_moment_resolvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:21:45.818431+00:00
-- url     : https://prove2.me/theorems/cefb902e-2dde-44af-8672-101e4d9b514d
-- title:
--   Exponential height moments and spatial resolvent of genuine killed first-record survival up to the positive Esscher-root threshold
-- statement:
--   Let T_h be the actual strict upward first-record clock and D_a the actual reflected drawdown ruin clock of a spectrally negative Levy process, with pure infinite-small-jump variation. For positive q and a and any positive Esscher root φ satisfying ψ(φ)=q, the spatial transform ∫_{h>0} exp(-θ h) E[exp(-q T_h); T_h<D_a] dh equals 1/(θ+W'(a)/W(a)) for every real θ>-φ, even negative θ. This proves finite positive exponential height moments for every growth rate below φ and includes the undamped potential.
-- source:
--   Proved genuine original-process exact G_a(h)=exp(-h W'(a)/W(a)) 1c71a04d; Proved slope lower bound W'/W≥φ a5dbcace; Mathlib integral_exp_mul_Ioi.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_spatial_exponential_moment_resolvent
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a θ : ℝ) (ha : 0 < a) (hθ : -φ < θ) :
    (∫ h : ℝ in Ioi 0,
      Real.exp (-(θ * h)) *
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal) =
    (θ + deriv W a / W a)⁻¹ := by sorry
