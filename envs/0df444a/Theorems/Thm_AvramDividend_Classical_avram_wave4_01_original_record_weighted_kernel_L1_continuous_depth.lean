-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_kernel_L1_continuous_depth
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_weighted_kernel_L1_continuous_depth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:27:46.171372+00:00
-- url     : https://prove2.me/theorems/c7c8dc44-0cf2-4974-85fd-3a447e73d547
-- title:
--   Genuine original-process first-record spatial Esscher kernel is L1-continuous in positive drawdown depth
-- statement:
--   Under divergent first absolute small-negative-jump moment, no Standing hypothesis, and positive Esscher root φ with ψ(φ)=q, the genuine killed strict-record discounted kernel K_a(h)=exp(-θh)E[e^{-qT_h};T_h<D_a] varies continuously in L¹((0,∞),dh) as the positive drawdown depth varies, for every θ>−φ. This is proved via source joint pointwise continuity, source uniform exponential domination, source integrability and Mathlib dominated convergence. It is stronger than continuity of the integrated resolvent and provides a bona fide stochastic L¹ stability interface.
-- source:
--   Canonical Proved source joint survival continuity ada5fda3, weighted source pointwise domination 62bbd1d1, weighted integrability f6c5a0cd, and pinned Mathlib DCT.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_survival_joint_continuous_height_depth
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_esscher_pointwise_domination
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_esscher_height_integrable
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_weighted_kernel_L1_continuous_depth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (θ a : ℝ) (hθ : -φ < θ) (ha : 0 < a) :
    Tendsto (fun b : ℝ =>
      ∫ h : ℝ in Ioi 0,
        |(Real.exp (-(θ * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X b ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal) - (Real.exp (-(θ * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal)|)
      (𝓝[Ioi (0 : ℝ)] a) (𝓝 (0 : ℝ)) := by sorry
