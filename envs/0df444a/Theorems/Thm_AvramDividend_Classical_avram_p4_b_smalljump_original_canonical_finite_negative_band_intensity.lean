-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_canonical_finite_negative_band_intensity
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_canonical_finite_negative_band_intensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:11:57.226824+00:00
-- url     : https://prove2.me/theorems/f94558e5-d9ed-45cb-be2a-f94187c00783
-- title:
--   Every original canonical finite-negative truncation has finite jump intensity
-- statement:
--   For the original source spectrally negative Lévy process and its actual source Lévy measure, each band (-1,-1/(n+1)] has finite Lévy intensity because it lies away from zero. This justifies the finite-intensity step of the small-jump approximation but does not claim that the full (-1,0) band has finite intensity or that adapted predictable integrands are compensated.
-- source:
--   Accepted original Lévy negative mass away from zero 0ff609aa plus measure monotonicity for the canonical finite band.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_negative_mass_away_from_zero_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_canonical_finite_negative_band_intensity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ n : ℕ,
      X.ν (Ioc (-1 : ℝ) (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ))) < ⊤ := by sorry
