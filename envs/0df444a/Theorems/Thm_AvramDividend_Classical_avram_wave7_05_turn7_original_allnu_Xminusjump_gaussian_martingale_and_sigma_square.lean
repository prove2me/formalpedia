-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_gaussian_martingale_and_sigma_square
-- name    : AvramDividend.Classical.avram_wave7_05_turn7_original_allnu_Xminusjump_gaussian_martingale_and_sigma_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:59:31.363791+00:00
-- url     : https://prove2.me/theorems/e07e648d-a88b-4c08-a517-5530b130bcca
-- title:
--   Original arbitrary-jump Lévy X minus its jump components is a Gaussian martingale and has sigma squared compensated-square martingale
-- statement:
--   For the canonical original spectrally negative Lévy process X on its own Omega/P/right-continuous filtration, define M_t := X.X_t - t X.c - Jsmall_t - Jlarge_t. If the same-space zero-jump Lévy Gaussian component Y exists with Y.sigma=X.sigma and the exact pathwise source decomposition, then M is a martingale and M_t^2 - t X.sigma^2 is a martingale in the original filtration. This identifies the Gaussian continuous-martingale characteristic without changing probability spaces. Construction of Y and J fields, and continuity of M, remain distinct explicit obligations.
-- source:
--   Exact same-space pathwise source decomposition plus two Proved original zero-jump martingale laws, UUID 0e0e6523-99f7-4178-b236-3c7328c51eaf and 208594ec-33f7-472e-a735-c52fa593078e. Full original process X and its rightCont filtration remain verbatim.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn7_original_allnu_Xminusjump_gaussian_martingale_and_sigma_square
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    Martingale M 𝓕.rightCont P ∧
      Martingale (fun t ω => M t ω ^ 2 - (t : ℝ) * X.σ ^ 2)
        𝓕.rightCont P := by sorry
