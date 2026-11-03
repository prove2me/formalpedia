-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn5_original_allnu_source_reserve_gaussian_jump_decomposition
-- name    : AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_source_reserve_gaussian_jump_decomposition
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T18:15:57.945323+00:00
-- url     : https://prove2.me/theorems/653fe960-c851-45fc-9b13-57bb43520d8e
-- title:
--   Original spectrally negative Lévy reserve splits into drift, same-filtration Gaussian and jumps minus actual dividends
-- statement:
--   For the actual original Lévy risk process with arbitrary Lévy jump measure, an explicit same-sample-space Gaussian-plus-jumps source decomposition implies an exact pathwise reserve identity subtracting the original dividend control. The hypothesis retains the entire source filtration, Lévy characteristics, stopping conventions and original reserve.
-- source:
--   Canonical AvramDividend.Classical.riskProcess and rightLimit D, with same-original-space decomposition. Does not assert existence of a Gaussian extraction; that is an explicit binder.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open AvramDividend.Classical MeasureTheory
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_source_reserve_gaussian_jump_decomposition
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
          Jsmall t ω + Jlarge t ω) - rightLimit D t ω := by sorry
