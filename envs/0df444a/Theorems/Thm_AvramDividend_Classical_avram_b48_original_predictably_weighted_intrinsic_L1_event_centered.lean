-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b48_original_predictably_weighted_intrinsic_L1_event_centered
-- name    : AvramDividend.Classical.avram_b48_original_predictably_weighted_intrinsic_L1_event_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:53:48.120197+00:00
-- url     : https://prove2.me/theorems/a34edd22-491e-47ab-9ca9-7419d562ba90
-- title:
--   True original finite-activity Levy weighted Gaussian and compensated jump stopped sums have initially centred L1 limits
-- statement:
--   On the original Levy probability space and right-continuous filtration, finite-range stopped original intrinsic Gaussian and compensated small negative-jump martingales admit predictable bounded-grid weighted sums. Any integrable-dominated a.e. limiting weighted source gains are integrable and have zero mean on every initial-filtration event.
-- source:
--   Proved B32 original finite-range intrinsic Gaussian/jump martingales and JB23 genuine predictable weighted stopped two-noise L1 centring.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
import Theorems.Thm_AvramDividend_Classical_avram_jb23_original_stopped_two_noise_L1_initial_centered_limits
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b48_original_predictably_weighted_intrinsic_L1_event_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hBound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (T : Finset ℝ≥0) (hRange : ∀ ω, τ ω ∈ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    ∃ (R J : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (R t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (𝓝 (J t ω))) ∧
      ∀ {ι : Type*} (S : ℕ → Finset ι)
        (a b : ℕ → ι → ℝ≥0)
        (WG WJ : ℕ → ι → Ω → ℝ),
        (∀ k, ∀ i ∈ S k, a k i ≤ b k i) →
        (∀ k, ∀ i ∈ S k, Measurable[𝓕.rightCont (a k i)] (WG k i)) →
        (∀ k, ∀ i ∈ S k, Measurable[𝓕.rightCont (a k i)] (WJ k i)) →
        (∀ k, ∀ i ∈ S k, Integrable (fun ω =>
          (if τ ω ≤ a k i then 0 else WG k i ω) *
            (R (b k i) ω - R (a k i) ω)) P) →
        (∀ k, ∀ i ∈ S k, Integrable (fun ω =>
          (if τ ω ≤ a k i then 0 else WJ k i ω) *
            (J (b k i) ω - J (a k i) ω)) P) →
        ∀ (Gseq Jseq : ℕ → Ω → ℝ),
        (∀ k ω, Gseq k ω =
          ∑ i ∈ S k, (if τ ω ≤ a k i then 0 else WG k i ω) *
            (R (b k i) ω - R (a k i) ω)) →
        (∀ k ω, Jseq k ω =
          ∑ i ∈ S k, (if τ ω ≤ a k i then 0 else WJ k i ω) *
            (J (b k i) ω - J (a k i) ω)) →
        ∀ (MG MJ BG BJ : Ω → ℝ),
        (∀ᵐ ω ∂P, Tendsto (fun k => Gseq k ω) atTop (𝓝 (MG ω))) →
        (∀ᵐ ω ∂P, Tendsto (fun k => Jseq k ω) atTop (𝓝 (MJ ω))) →
        Integrable BG P → Integrable BJ P →
        (∀ k, ∀ᵐ ω ∂P, ‖Gseq k ω‖ ≤ BG ω) →
        (∀ k, ∀ᵐ ω ∂P, ‖Jseq k ω‖ ≤ BJ ω) →
        Integrable (fun ω => MG ω + MJ ω) P ∧
        (∫ ω in A, MG ω + MJ ω ∂P) = 0 := by sorry
