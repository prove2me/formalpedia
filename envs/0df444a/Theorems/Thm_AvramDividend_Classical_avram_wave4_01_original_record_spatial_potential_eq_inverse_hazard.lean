-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_spatial_potential_eq_inverse_hazard
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_spatial_potential_eq_inverse_hazard
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:32:47.473568+00:00
-- url     : https://prove2.me/theorems/1bc8ca04-1571-40a3-998e-8ddd8b9b9d8f
-- title:
--   Positive-record-height potential of actual reflected-killed first-record discount is the inverse logarithmic scale slope
-- statement:
--   For the actual strict upward record time T_h and actual reflected drawdown killing time D_a at fixed a>0, the spatial potential ∫_0^infty E[e^{-q T_h};T_h<D_a] dh is exactly 1 / (W'(a)/W(a)), the inverse genuine killed first-record hazard. The proved source exponential identity identifies the integrand for positive record heights, the proved Esscher root bound makes the slope strictly positive, and Mathlib's exact real exponential-tail integral evaluates the potential. No Standing hypothesis, proxy excursion or stochastic axiom.
-- source:
--   Proved actual killed-record exponential log-scale derivative 1c71a04d-268a-4126-b1bd-c0537bda0db1 and positive root slope lower bound a5dbcace-268f-44a5-a46e-c42f4470ceb3, pinned Mathlib integral_exp_mul_Ioi.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_spatial_potential_eq_inverse_hazard
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a : ℝ) (ha : 0 < a) :
    (∫ h : ℝ in Ioi 0,
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal) =
    (deriv W a / W a)⁻¹ := by sorry
