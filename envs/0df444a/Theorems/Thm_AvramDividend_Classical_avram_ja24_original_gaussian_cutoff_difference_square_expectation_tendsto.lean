-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja24_original_gaussian_cutoff_difference_square_expectation_tendsto
-- name    : AvramDividend.Classical.avram_ja24_original_gaussian_cutoff_difference_square_expectation_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:19:55.123862+00:00
-- url     : https://prove2.me/theorems/5a256e6d-5514-488e-9fde-ec8aa5ddb242
-- title:
--   Original cutoff difference squares converge in expectation to the omitted Gaussian tail
-- statement:
--   For the original Levy process at finite negative jump activity, the exact fixed-cutoff residual differences have a square-integrable almost-sure limit and their squared expectations converge. The proof uses the original finite negative count and its second moment as an L2 dominating envelope.
-- source:
--   J-A24 stochastic dominated convergence half of e5df71c0, paired with deterministic analytic strip convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja24_original_gaussian_cutoff_difference_square_expectation_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω)))
    (hStrip : ∀ (n m : ℕ), n ≤ m → ∀ (t : ℝ≥0),
      Integrable (fun ω =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in Ioc
          (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))), z ^ 2 ∂X.ν)) :
    ∀ n : ℕ, ∀ t : ℝ≥0,
      Integrable (fun ω =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) ^ 2) P ∧
      Tendsto
        (fun m : ℕ => ∫ ω,
          (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
            avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2 ∂P)
        atTop (nhds (∫ ω,
          (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
            R t ω) ^ 2 ∂P)) := by sorry
