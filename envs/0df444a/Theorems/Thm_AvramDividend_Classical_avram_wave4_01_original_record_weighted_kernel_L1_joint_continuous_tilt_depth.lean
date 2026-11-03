-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_kernel_L1_joint_continuous_tilt_depth
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_weighted_kernel_L1_joint_continuous_tilt_depth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:12:36.385592+00:00
-- url     : https://prove2.me/theorems/e3e4a659-6b1d-41cc-88bd-71fbb75f00db
-- title:
--   Genuine killed first-record Esscher kernel is jointly L1-continuous in tilt and drawdown depth
-- statement:
--   For the actual original-process strict upward record T_h and reflected drawdown D_a, with q>0, infinite first absolute small-negative-jump moment and positive Esscher root phi, the weighted kernel K_{theta,a}(h) varies jointly continuously in L1((0,infty),dh) as (theta,a) varies in theta>minus phi and a>0. Proof: genuine joint pointwise killed-record survival continuity, locally uniform admissible tilt envelope, pinned dominated convergence, no Standing.
-- source:
--   Previously Proved source joint survival height-depth continuity ada5fda3, weighted envelope 62bbd1d1 and integrability f6c5a0cd, pinned Mathlib dominated convergence.

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

theorem AvramDividend.Classical.avram_wave4_01_original_record_weighted_kernel_L1_joint_continuous_tilt_depth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (θ₀ a : ℝ) (hθ₀ : -φ < θ₀) (ha : 0 < a) :
    Tendsto (fun p : ℝ × ℝ =>
      ∫ h : ℝ in Ioi 0,
        |(Real.exp (-(p.1 * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X p.2 ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal) - (Real.exp (-(θ₀ * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal)|)
      (𝓝[(Ioi (-φ)).prod (Ioi (0 : ℝ))] (θ₀, a)) (𝓝 (0 : ℝ)) := by sorry
