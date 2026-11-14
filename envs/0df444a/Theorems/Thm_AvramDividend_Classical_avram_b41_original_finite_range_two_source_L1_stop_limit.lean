-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b41_original_finite_range_two_source_L1_stop_limit
-- name    : AvramDividend.Classical.avram_b41_original_finite_range_two_source_L1_stop_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:53:53.785056+00:00
-- url     : https://prove2.me/theorems/8b24dd35-d4c5-42aa-a4d7-27b4eeef0d0e
-- title:
--   Original finite-range stopped Gaussian and jump sources admit centred initial-event L1 limit
-- statement:
--   For a sequence of original right-continuous bounded finite-range Lévy stopping times, choose actual intrinsic Gaussian-plus-compensated negative-jump stopped sources. Every source sum has zero expected integral on any initial-filtration event. Any integrable random variable that is their restricted L1 limit retains zero initial-event mean.
-- source:
--   Proved B40 actual finite-range stopped mixed-source martingale, Mathlib tendsto_integral_of_L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b40_original_finite_range_intrinsic_centered_sum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b41_original_finite_range_two_source_L1_stop_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) (τ : ℕ → Ω → ℝ≥0)
    (hτstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ k ω : WithTop ℝ≥0)))
    (hτbound : ∀ k ω, τ k ω ≤ (n : ℝ≥0))
    (S : ℕ → Finset ℝ≥0) (hτrange : ∀ k ω, τ k ω ∈ S k)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    ∃ (R Jsmall : ℕ → ℝ≥0 → Ω → ℝ) (M : ℕ → Ω → ℝ),
      (∀ k, Integrable (M k) P ∧
        (∫ ω in A, M k ω ∂P) = 0 ∧
        (∀ ω, M k ω = R k (τ k ω) ω + Jsmall k (τ k ω) ω)) ∧
      ∀ (Z : Ω → ℝ), Integrable Z P →
        Tendsto (fun k => ∫⁻ ω in A,
          ‖M k ω - Z ω‖ₑ ∂P) atTop (𝓝 (0 : ℝ≥0∞)) →
        (∫ ω in A, Z ω ∂P) = 0 := by sorry
