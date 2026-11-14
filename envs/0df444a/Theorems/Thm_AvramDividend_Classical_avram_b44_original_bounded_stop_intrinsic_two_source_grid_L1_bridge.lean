-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b44_original_bounded_stop_intrinsic_two_source_grid_L1_bridge
-- name    : AvramDividend.Classical.avram_b44_original_bounded_stop_intrinsic_two_source_grid_L1_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:03:56.421303+00:00
-- url     : https://prove2.me/theorems/307f6934-ae26-419f-92f8-8e37269623b5
-- title:
--   Original bounded stopped Levy source admits finite-valued upper-clock mixed centred approximations with L1 limit
-- statement:
--   For a genuine finite-activity spectrally negative Levy process and any bounded right-continuous original stopping time, construct finite-valued upper-grid stopping times converging pathwise to it and initially centred intrinsic Gaussian-plus-compensated-jump stopped terms. Every integrable restricted L1 limit of these true source terms retains zero mean on every initial-filtration event.
-- source:
--   Proved ja18 finite upper stopping-grid approximation 40599988, B41 same-source mixed finite-range L1 limit 8b24dd35.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_rightcont_upper_grid_stops
import Theorems.Thm_AvramDividend_Classical_avram_b41_original_finite_range_two_source_L1_stop_limit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b44_original_bounded_stop_intrinsic_two_source_grid_L1_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    ∃ (ρ : ℕ → Ω → ℝ≥0) (S : ℕ → Finset ℝ≥0)
      (R Jsmall : ℕ → ℝ≥0 → Ω → ℝ) (M : ℕ → Ω → ℝ),
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, ρ k ω ∈ S k) ∧
      (∀ k ω, τ ω ≤ ρ k ω ∧ ρ k ω ≤ (n : ℝ≥0)) ∧
      (∀ ω, Tendsto (fun k => ρ k ω) atTop (𝓝 (τ ω))) ∧
      (∀ k, Integrable (M k) P ∧
        (∫ ω in A, M k ω ∂P) = 0 ∧
        (∀ ω, M k ω =
          R k (ρ k ω) ω + Jsmall k (ρ k ω) ω)) ∧
      (∀ (Z : Ω → ℝ), Integrable Z P →
        Tendsto (fun k => ∫⁻ ω in A,
          ‖M k ω - Z ω‖ₑ ∂P) atTop (𝓝 (0 : ℝ≥0∞)) →
        (∫ ω in A, Z ω ∂P) = 0) := by sorry
