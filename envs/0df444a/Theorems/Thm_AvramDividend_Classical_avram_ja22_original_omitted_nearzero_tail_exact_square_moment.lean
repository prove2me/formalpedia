-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja22_original_omitted_nearzero_tail_exact_square_moment
-- name    : AvramDividend.Classical.avram_ja22_original_omitted_nearzero_tail_exact_square_moment
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T15:57:47.037861+00:00
-- url     : https://prove2.me/theorems/1679c8a4-9da6-4117-9656-1783d3981201
-- title:
--   Original omitted near-zero compensated jump residual has exact Levy-tail variance
-- statement:
--   For the same original residual limit, the difference of finite truncation and limit is exactly the omitted near-zero compensated jump tail. Establish its integrable square and exact near-zero Levy-band second moment.
-- source:
--   J-A22 corrected physical stochastic decomposition of ebbab4df; replaces quarantined J-A21 fixed cutoff moment claims. Proved 0d7f9ed2 supplies the original sample path limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja22_original_omitted_nearzero_tail_exact_square_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ (n : ℕ) (t : ℝ≥0),
      Integrable (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) ^ 2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by sorry
