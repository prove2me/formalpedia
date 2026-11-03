-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn5_original_allnu_source_reserve_gaussian_jump_decomposition_exact_D
-- name    : AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_source_reserve_gaussian_jump_decomposition_exact_D
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:26:11.593198+00:00
-- url     : https://prove2.me/theorems/87142cc1-dd03-4e85-a675-3421b237940f
-- title:
--   Original spectrally negative Lévy reserve splits into drift, same-filtration Gaussian and jumps minus actual dividends
-- statement:
--   Exact original-source controlled reserve decomposition, with canonical current-time dividend payout D t ω, for arbitrary Lévy jump measure. The same-space Gaussian extraction remains an explicit assumption.
-- source:
--   Canonical riskProcess subtracts D t ω at the current time, not rightLimit D t ω; explicitly preserve that distinction while inserting original same-space Gaussian+jump decomposition.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open AvramDividend.Classical MeasureTheory
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_source_reserve_gaussian_jump_decomposition_exact_D
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (u : ℝ≥0) (η : Ω),
      X.X u η = (u : ℝ) * X.c +
        (Y.X u η - (u : ℝ) * Y.c) + Jsmall u η + Jlarge u η)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (t : ℝ≥0) (ω : Ω) :
    riskProcess X x D t ω =
      x + ((t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) +
          Jsmall t ω + Jlarge t ω) - D t ω := by sorry
