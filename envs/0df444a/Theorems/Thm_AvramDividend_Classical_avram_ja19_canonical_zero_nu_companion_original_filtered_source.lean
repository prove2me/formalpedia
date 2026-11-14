-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja19_canonical_zero_nu_companion_original_filtered_source
-- name    : AvramDividend.Classical.avram_ja19_canonical_zero_nu_companion_original_filtered_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T12:47:15.700267+00:00
-- url     : https://prove2.me/theorems/153204a0-82f2-4566-bbf6-45b137f6dd9b
-- title:
--   Original-filtered finite-activity Gaussian companion with intrinsic cutoff convergence
-- statement:
--   Under original finite negative jump activity, construct a full zero-nu spectrally negative Levy process Y on exactly the original Omega, P and filtration with sigma equal to X.sigma, such that the physical intrinsic compensated Gaussian residual cutoffs converge to Y.X_t-tY.c simultaneously for all horizons almost surely. No auxiliary or independent Gaussian noise is allowed. This canonical construction does not quantify over an arbitrary postulated limit R.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i); Kyprianou Fluctuations of Levy Processes, Levy-Ito decomposition, requires intrinsic removal of the original finite negative jump process with correct compensator and original-filtration independence. Parent c5c7c200 and Proved original cutoff-limit uniqueness 0f2f4abf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja19_canonical_zero_nu_companion_original_filtered_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      Y.ν = 0 ∧ Y.σ = X.σ ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto
          (fun k : ℕ =>
            avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (Y.X t ω - (t : ℝ) * Y.c))) := by sorry
