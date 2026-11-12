-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18p_original_J_rightcont_integrable_envelope
-- name    : AvramDividend.Classical.avram_ja18p_original_J_rightcont_integrable_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:39:57.830205+00:00
-- url     : https://prove2.me/theorems/3a480565-15d9-41fc-b8ac-e0d4fc04dfaf
-- title:
--   Original centred jump residual has right-continuous paths and integrable bounded-horizon envelope
-- statement:
--   For finite negative-jump activity, the original jump residual X_t - t E[X_1] - R_t is a finite-activity compensated jump path on the original probability space. Establish right-continuous paths, zero origin and integrable pathwise sup bound for bounded horizon. The proved generic optional-sampling theorem 2d92580d then yields the stopped J certificate.
-- source:
--   J-A18 original compensated stopped jump martingale 41babf55

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18p_original_J_rightcont_integrable_envelope
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
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (n : ℕ) (hn : 0 < n) :
    let μ : ℝ := ∫ ω, X.X 1 ω ∂P
    let J : ℝ≥0 → Ω → ℝ :=
      fun t ω => X.X t ω - (t : ℝ) * μ - R t ω
    ∃ B : Ω → ℝ, Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => J u ω) (Set.Ici t) t) ∧
      (∀ᵐ ω ∂P, J 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
        ‖J t ω‖ ≤ B ω) := by sorry
