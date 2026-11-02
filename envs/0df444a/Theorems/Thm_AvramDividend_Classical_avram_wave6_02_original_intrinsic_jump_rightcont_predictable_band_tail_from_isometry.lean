-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_intrinsic_jump_rightcont_predictable_band_tail_from_isometry
-- name    : AvramDividend.Classical.avram_wave6_02_original_intrinsic_jump_rightcont_predictable_band_tail_from_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:25:48.38857+00:00
-- url     : https://prove2.me/theorems/14effb90-47c2-431a-ba24-b21a6112acd9
-- title:
--   Original intrinsic Lévy jump compensated finite-band isometry tail in the right-continuous predictable filtration
-- statement:
--   Source-exact right-continuous predictable version of the Proved original intrinsic jump source isometry-to-tail implication. The measurable space of the kernel is (𝓕.rightCont.predictable).prod Borel, matching the actual stopped C² Taylor kernel, and the intrinsic NX is defined literally from jumps of X. Under explicit centered linear source L² isometry and literal finite-band source representation, the compensated finite bands have a centered L²(P) limit and the exact tail inequality. No surrogate source space or first small-jump moment is introduced.
-- source:
--   Proved d0e721e0 source isometry-to-tail proof, with its unused hAll equality changed from 𝓕.predictable to 𝓕.rightCont.predictable to align with actual ruin stopped kernel 0e0663b1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_actual_probability_l2_stopped_band_limit_mean_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_02_original_intrinsic_jump_rightcont_predictable_band_tail_from_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    [mAll : MeasurableSpace ((ℝ≥0 × Ω) × ℝ)]
    (μ : Measure ((ℝ≥0 × Ω) × ℝ))
    (hAll : mAll = (𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ))
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ) (hGm : Measurable G)
    (hG : MemLp G (2 : ℝ≥0∞) μ)
    (hEnergy : ∫⁻ p, ‖G p‖ₑ ^ (2 : ℝ) ∂μ < ∞)
    (B : ℕ → Set ((ℝ≥0 × Ω) × ℝ))
    (hB : ∀ n, MeasurableSet (B n))
    (hBfinite : ∀ n, μ (B n) < ∞)
    (hBmono : Monotone B) (hBcover : (⋃ n, B n) = Set.univ)
    (I : Lp ℝ (2 : ℝ≥0∞) μ →ₗ[ℝ] Lp ℝ (2 : ℝ≥0∞) P)
    (hIso : ∀ v, ‖I v‖ = ‖v‖)
    (hZero : ∀ v, ∫ ω, I v ω ∂P = 0)
    (clock : Measure ℝ≥0)
    (hSource : ∀ n,
      (I ((hG.indicator (hB n)).toLp ((B n).indicator G)) : Ω → ℝ)
        =ᵐ[P] fun ω =>
      (∫ p, (B n).indicator G ((p.1, ω), p.2) ∂(NX ω)) -
        ∫ t, ∫ z, (B n).indicator G ((t, ω), z) ∂X.ν ∂clock) :
    ∃ Llimit : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto (fun n => I ((hG.indicator (hB n)).toLp
        ((B n).indicator G))) atTop (𝓝 Llimit) ∧
      (∫ ω, Llimit ω ∂P) = 0 ∧
      (∀ m n, m ≤ n →
        dist (I ((hG.indicator (hB m)).toLp ((B m).indicator G)))
          (I ((hG.indicator (hB n)).toLp ((B n).indicator G))) ≤
          (eLpNorm ((B m)ᶜ.indicator G) (2 : ℝ≥0∞) μ).toReal) ∧
      (∀ n,
        (I ((hG.indicator (hB n)).toLp ((B n).indicator G)) : Ω → ℝ)
          =ᵐ[P] fun ω =>
        (∫ p, (B n).indicator G ((p.1, ω), p.2) ∂(NX ω)) -
          ∫ t, ∫ z, (B n).indicator G ((t, ω), z) ∂X.ν ∂clock) := by sorry
