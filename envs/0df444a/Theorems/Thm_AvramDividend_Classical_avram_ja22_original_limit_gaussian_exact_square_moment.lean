-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja22_original_limit_gaussian_exact_square_moment
-- name    : AvramDividend.Classical.avram_ja22_original_limit_gaussian_exact_square_moment
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T15:57:34.589288+00:00
-- url     : https://prove2.me/theorems/2c95ecd3-cc44-4a7b-8127-2e962a252521
-- title:
--   Original intrinsic residual limit has exact sigma-square second moment
-- statement:
--   For an almost surely selected original intrinsic residual limit, establish square-integrability and exact Gaussian sigma-square variance, with no auxiliary Brownian identification.
-- source:
--   J-A22 corrected physical stochastic decomposition of ebbab4df; replaces quarantined J-A21 fixed cutoff moment claims. Proved 0d7f9ed2 supplies the original sample path limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja22_original_limit_gaussian_exact_square_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 := by sorry
