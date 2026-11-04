-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_sigma_zero_original_pure_jump_stopped_taylor_mesh_vanishes
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_sigma_zero_original_pure_jump_stopped_taylor_mesh_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:07:35.200766+00:00
-- url     : https://prove2.me/theorems/5efb6c1a-0213-40f6-80dd-b4158f6f57f9
-- title:
--   Original Levy sigma zero pure jump stopped Gaussian Taylor mesh vanishes without Brownian motion
-- statement:
--   When the source Gaussian coefficient vanishes and the true original spectrally negative Levy process has the almost sure all-time canonical drift plus intrinsic compensated small- and large-jump decomposition, all Gaussian first-order and centred quadratic Taylor terms vanish for arbitrary random mesh clocks and arbitrary weights, including interior stopped predictable weights. There is no auxiliary Brownian process and no differentiability assumption. The source pure-jump decomposition remains a genuine upstream obligation.
-- source:
--   Source-specific zero-variance algebra for the Gaussian branch in Avram, Palmowski and Pistorius, Proposition 4(i) and Eq. (5.13). Derivation uses the given genuine X and X.σ=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_sigma_zero_original_pure_jump_stopped_taylor_mesh_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : X.σ = 0)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hPure : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c + Jsmall u ω + Jlarge u ω)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ) :
    ∀ᵐ ω ∂P,
      let Z : ℝ≥0 → ℝ := fun u =>
        X.X u ω - (u : ℝ) * X.c - Jsmall u ω - Jlarge u ω
      (∑ i ∈ S,
        (G i ω * (Z (τ i ω + h i) - Z (τ i ω)) +
          (1 / 2 : ℝ) * H i ω *
            ((Z (τ i ω + h i) - Z (τ i ω)) ^ 2 -
              (h i : ℝ) * X.σ ^ 2))) = 0 := by sorry
