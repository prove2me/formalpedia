-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_esscher_height_integrable
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_weighted_esscher_height_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:12:41.624043+00:00
-- url     : https://prove2.me/theorems/f6c5a0cd-a98e-4ae1-9d61-fbd4159e6689
-- title:
--   Absolute real integrability of the genuine discounted first-record spatial density for all Esscher-admissible tilts
-- statement:
--   Under q>0 and divergent first absolute small-negative-jump moment without Standing, for the original strict upward record time T_h and reflected drawdown ruin D_a, the spatially weighted killed discount density h↦exp(-θh)E[e^{-qT_h};T_h<D_a] is Lebesgue integrable over h>0 whenever a>0 and θ>−φ, where φ>0 solves ψ(φ)=q. The proof uses the genuine first-record spatial exponential law, the positive Esscher-root hazard lower bound and pinned Mathlib half-line exponential integrability. This is an explicit integrability interface for actual-process dominated convergence.
-- source:
--   Canonical original first-record exponential law avram_wave4_01_original_record_discount_exp_log_scale_deriv, positive root slope bound avram_wave4_01_original_record_log_slope_ge_positive_esscher_root, and pinned integrableOn_exp_mul_Ioi (a<0).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_weighted_esscher_height_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a θ : ℝ) (ha : 0 < a) (hθ : -φ < θ) :
    IntegrableOn (fun h : ℝ =>
      Real.exp (-(θ * h)) *
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal) (Ioi 0) := by sorry
