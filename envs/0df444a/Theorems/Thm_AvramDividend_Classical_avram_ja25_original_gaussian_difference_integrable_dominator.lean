-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja25_original_gaussian_difference_integrable_dominator
-- name    : AvramDividend.Classical.avram_ja25_original_gaussian_difference_integrable_dominator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:34:09.088024+00:00
-- url     : https://prove2.me/theorems/7faf2af4-b98a-4372-b7da-9c3a1d65faaf
-- title:
--   Original two-cutoff Gaussian square differences share an integrable finite-count dominator
-- statement:
--   At finite original negative jump activity, use the original finite negative count L2 theorem and the original pathwise cutoff convergence bound to dominate all squared cutoff differences at a fixed source cutoff by a single integrable envelope, without auxiliary Gaussian noise.
-- source:
--   J-A25 physical DCT helper for the original Gaussian omitted-tail variance e5df71c0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja25_original_gaussian_difference_integrable_dominator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω)))
    (n : ℕ) (t : ℝ≥0) :
    ∃ G : Ω → ℝ, Integrable G P ∧
      ∀ k : ℕ, ∀ᵐ ω ∂P,
        ‖(avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω) ^ 2‖ ≤ G ω := by sorry
