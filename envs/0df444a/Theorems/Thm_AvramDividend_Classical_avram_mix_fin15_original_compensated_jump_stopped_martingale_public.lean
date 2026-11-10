-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin15_original_compensated_jump_stopped_martingale_public
-- name    : AvramDividend.Classical.avram_mix_fin15_original_compensated_jump_stopped_martingale_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-09T13:05:35.328449+00:00
-- url     : https://prove2.me/theorems/41babf55-7865-45fb-a343-5c6b60baf089
-- title:
--   Original finite-activity compensated jump source is a stopped martingale in its own filtration (public route)
-- statement:
--   Subtract the actual compact-uniform original Gaussian residual and the integrable deterministic mean drift from the original mixed Lévy path. Identify the complementary finite-activity compensated jump component as an original-filtration martingale, with integrable bounded stopped value and initial-filtration conditional mean zero. The source-limit condition prevents replacement by an unrelated Brownian process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin15_original_compensated_jump_stopped_martingale_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0)) :
    let μ : ℝ := ∫ ω, X.X 1 ω ∂P
    let J : ℝ≥0 → Ω → ℝ :=
      fun t ω => X.X t ω - (t : ℝ) * μ - R t ω
    (∀ t : ℝ≥0, Integrable (J t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (J t) ω = J s ω) ∧
      Integrable (fun ω => J (τ ω) ω) P ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P
          (fun ω => J (τ ω) ω) ω = 0) := by sorry
