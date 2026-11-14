-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_positive_sigma_intrinsic_limit_true_same_filtration_gaussian_companion
-- name    : AvramDividend.Classical.avram_a22_original_positive_sigma_intrinsic_limit_true_same_filtration_gaussian_companion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T16:04:51.580197+00:00
-- url     : https://prove2.me/theorems/df38ef33-7456-45c1-a6e7-99a36dd408c3
-- title:
--   Positive original Gaussian variance same-filtration Lévy companion constructed from the actual physical residual limit
-- statement:
--   The unresolved genuinely Gaussian positive-variance branch of original finite-activity Lévy–Itô decomposition. For every spectrally negative Lévy process with strictly positive σ and its true intrinsic truncated physical residual limit R on the original Ω,P,filtration, construct Y on that same space and filtration satisfying all structural Lévy requirements: no positive jumps, every-path càdlàg, adaptedness, stationary independent increments with respect to the original past, correct zero Lévy measure and σ, full Laplace law, and almost-sure all-time identity R=Y.X-tY.c. No extension of the probability space and no invented independent Brownian motion.
-- source:
--   Avram Palmowski Pistorius 2007, Lévy–Itô decomposition; Proved original limit 3a9ebf2b, source compensated martingale 6bbd3299; remaining c5c7 branch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_positive_sigma_intrinsic_limit_true_same_filtration_gaussian_companion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hSigma : 0 < X.σ) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      Y.ν = 0 ∧ Y.σ = X.σ ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        R t ω = Y.X t ω - (t : ℝ) * Y.c) := by sorry
