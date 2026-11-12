-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja19_original_zero_nu_process_from_finite_jump_source
-- name    : AvramDividend.Classical.avram_ja19_original_zero_nu_process_from_finite_jump_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T12:35:58.421333+00:00
-- url     : https://prove2.me/theorems/ca457ff7-664b-4735-9fd3-6d32cb0e31d0
-- title:
--   Remove original finite-activity jumps to obtain a same-filtration zero-Lévy-measure process
-- statement:
--   Given the actual original finite-band compensated jump limit Jsmall, remove Jsmall and the actual large-jump process, with deterministic drift correction, from the original Lévy process. Prove that the resulting original-space process is spectrally negative Lévy with zero Lévy measure, Gaussian coefficient exactly X.sigma, and its centred values recover the original zero-cutoff residual after adding Jsmall. Preserve right-continuous filtration, adaptedness, stationary independent increments, càdlàg paths and Laplace exponent. No stochastic process on another probability space is introduced.
-- source:
--   J-A19 original physical Lévy-Itô finite activity, source Proved 9362895e, 41babf55, 7dbfa029

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja19_original_zero_nu_process_from_finite_jump_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hSource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω))) :
    ∃ (Y : SpectrallyNegativeLevy P 𝓕),
      Y.ν = 0 ∧ Y.σ = X.σ ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
          (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω) := by sorry
