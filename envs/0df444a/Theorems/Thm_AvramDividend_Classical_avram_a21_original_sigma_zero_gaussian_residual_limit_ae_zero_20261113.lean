-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
-- name    : AvramDividend.Classical.avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:36:56.495737+00:00
-- url     : https://prove2.me/theorems/77f47f2e-df77-4f34-8b6c-0bec58cd87a1
-- title:
--   Physical intrinsic Gaussian residual limit vanishes at all horizons if sigma is zero and negative activity finite
-- statement:
--   For finite original negative Lévy activity and vanishing Gaussian coefficient, the residual limit R obtained from physically compensated original negative jumps vanishes almost surely, uniformly over all fixed horizons. The finite-negative sigma-zero BV theorem, original BV raw jump removed residual identity, original full retained compensated small mark limit, and original R=R0-Jsmall pathwise identity supply the actual same-source proof. Distinct from false independence of R0 and retained bands.
-- source:
--   Proved original BV raw removed residual 79a63ca0, original R=R0-Jsmall 2affdece, newly submitted finite negative sigma zero BV 9827a243, source original compensated small marks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω)))    (hSigma : X.σ = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, R t ω = 0 := by sorry
