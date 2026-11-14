-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_positive_sigma_nonzero_nu_intrinsic_true_same_filtration_gaussian_companion
-- name    : AvramDividend.Classical.avram_a22_original_positive_sigma_nonzero_nu_intrinsic_true_same_filtration_gaussian_companion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T16:17:09.382804+00:00
-- url     : https://prove2.me/theorems/fa8ec983-ec9a-428e-b4d8-8c8e433ce5b7
-- title:
--   Original nonzero negative Lévy marks and strictly positive Gaussian variance: genuine filtered same-source Lévy companion
-- statement:
--   The irreducible nontrivial Lévy–Itô source construction for the original positive-Gaussian finite-negative-activity process with nonzero negative mark measure. From the actual intrinsic compensated source cutoff residual R on the original Ω,P,𝓕, construct a genuine zero-ν original-filtration Lévy process Y carrying exactly σ=X.σ, with paths càdlàg for every sample point, adaptedness, correct filtration-independent stationary increments, full Laplace transform, and a.s. simultaneous all-time equality R=Y.X-tY.c. For ν=0 the construction is solved by taking Y=X itself; this child isolates ν≠0 as the sole remaining positive-σ stochastic source obligation. No extension of probability space or independent Gaussian injection is permitted.
-- source:
--   Original target df38 positive-sigma branch; actual Lévy–Itô decomposition, Kyprianou Lévy processes; original zero-ν companion branch and Proved original cutoff convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_positive_sigma_nonzero_nu_intrinsic_true_same_filtration_gaussian_companion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hSigma : 0 < X.σ) (hNu : X.ν ≠ 0) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      Y.ν = 0 ∧ Y.σ = X.σ ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        R t ω = Y.X t ω - (t : ℝ) * Y.c) := by sorry
