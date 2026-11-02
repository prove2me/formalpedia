-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_source_compensated_band_tail_from_isometry
-- name    : AvramDividend.Classical.avram_wave5_02b_source_compensated_band_tail_from_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:13:37.163661+00:00
-- url     : https://prove2.me/theorems/d0e721e0-f545-482b-8fa3-d0611e74f2a8
-- title:
--   Original-source compensated band tail from a source L2 isometry
-- statement:
--   Given a centred linear L2 isometry for the original predictable kernel energy measure and its explicit identification with the original intrinsic-jump integral minus the pathwise compensator on each band, the stochastic band-difference tail is bounded by the same kernel's original predictable energy outside the smaller band. The centred actual-source L2 limit follows from the Proved sigma-finite band theorem. The source isometry, physical energy measure identification, and source representation are explicit assumptions; no band-difference bound is assumed.
-- source:
--   Proved actual probability sigma-finite L2 limit 540bd939-b21d-4883-901a-fc40fbf58ec6 and Lp indicator monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_actual_probability_l2_stopped_band_limit_mean_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02b_source_compensated_band_tail_from_isometry
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
    (hAll : mAll = (𝓕.predictable).prod
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
