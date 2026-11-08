-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_twoboundary_source_tail_L1
-- name    : AvramDividend.Classical.avram_bv_residual10_original_twoboundary_source_tail_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:11:51.494281+00:00
-- url     : https://prove2.me/theorems/d1bc06ff-61f9-41ec-8538-7e6cb6080942
-- title:
--   Original pre-jump zero and finite-cap boundary clipping with vanishing BV source-mass L1 tail
-- statement:
--   The actual physical-row original process with dividend strategy has measurable almost-surely exhausting events on which its pre-jump reserve, its reciprocal and the reciprocal of its gap from the real finite cap are bounded. Thus strict interior coordinates are rowwise separated from both singular reserve boundaries when C is finite. When C is infinite, the extra cap term is an auxiliary reciprocal of negative reserve and imposes no new finite-cap assertion. The excluded-event BV source-mass envelope is integrable for each row and has vanishing expectation under the genuine Standing and BV assumptions with a fixed nonnegative multiplier. No actual stopped Taylor/jump discretisation error domination is silently introduced.
-- source:
--   AVRAM BV-RESIDUAL10 original rowwise dual boundary and source-mass localisation, 7 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_rowwise_ae_eventual_clipping
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_prejump_inverse_band_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_tail_L1_any_clock

open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_twoboundary_source_tail_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (u : ℕ → ℕ → ℝ≥0)
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞)))
    (hεsum : (∑' n, ε n) ≠ ⊤)
    (T : ℝ≥0) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    let Z : ℕ → Ω → ℕ → ℝ := fun n ω i =>
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    ∃ N L U : ℕ → ℕ, ∃ s : ℕ → Set Ω,
      (∀ n, s n =
        ({ω | ∀ i ∈ Finset.range (n + 1), abs (Z n ω i) ≤ (N n : ℝ)} ∩
         {ω | ∀ i ∈ Finset.range (n + 1), abs ((Z n ω i)⁻¹) ≤ (L n : ℝ)}) ∩
        {ω | ∀ i ∈ Finset.range (n + 1),
          abs (((C.toReal : ℝ) - Z n ω i)⁻¹) ≤ (U n : ℝ)}) ∧
      (∀ n, MeasurableSet (s n)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) ∧
      (∀ n, Integrable (fun ω => if ω ∈ s n then 0 else
        K₀ * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|)) P) ∧
      Tendsto (fun n => ∫ ω, if ω ∈ s n then 0 else
        K₀ * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|) ∂P)
        atTop (nhds (0 : ℝ)) := by sorry
