-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_kernel_L1_continuous_tilt
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_weighted_kernel_L1_continuous_tilt
-- status  : Open
-- author  : @WillR
-- created : 2026-10-31T22:09:09.742924+00:00
-- url     : https://prove2.me/theorems/1f80482e-d440-40ed-90d0-0c08d95bfc86
-- title:
--   Genuine killed first-record Esscher kernel is L1-continuous in admissible spatial tilt
-- statement:
--   With actual strict upward record time and reflected drawdown clock, positive discount q, divergent absolute small-negative-jump first moment, no Standing, and positive Esscher root phi, the weighted killed-record spatial height kernel is continuous in L1((0,infty),dh) as the real tilt varies within theta>minus phi. The proof uses a locally uniform integrable exponential envelope and dominated convergence.
-- source:
--   Canonical source first-record weighted envelope and integrability, pinned Mathlib DCT; preliminary step for joint L1 (tilt,depth) continuity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_esscher_pointwise_domination
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_esscher_height_integrable
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_weighted_kernel_L1_continuous_tilt
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a θ₀ : ℝ) (ha : 0 < a) (hθ₀ : -φ < θ₀) :
    Tendsto (fun θ : ℝ =>
      ∫ h : ℝ in Ioi 0,
        |(Real.exp (-(θ * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal) - (Real.exp (-(θ₀ * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal)|)
      (𝓝[Ioi (-φ)] θ₀) (𝓝 (0 : ℝ)) := by sorry
