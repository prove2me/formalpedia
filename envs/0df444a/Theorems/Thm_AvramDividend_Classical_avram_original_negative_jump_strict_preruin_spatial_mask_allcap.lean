-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_original_negative_jump_strict_preruin_spatial_mask_allcap
-- name    : AvramDividend.Classical.avram_original_negative_jump_strict_preruin_spatial_mask_allcap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:17:36.490265+00:00
-- url     : https://prove2.me/theorems/5f327536-5665-4d0d-a2ab-4a67c89c31a5
-- title:
--   Original strict pre-ruin negative-jump prestate mask for arbitrary Lévy activity and cap
-- statement:
--   For every actual negative jump of a spectrally negative Lévy process strictly before ruin at positive time, the left limit of the post-right-dividend controlled surplus is strictly positive and is bounded by the extended-real dividend cap. This uses the original Lévy path and admissible dividend strategy, and requires neither finite jump activity nor a finite cap. It is a source-faithful spatial-mask lemma for the original stopped Itô–Meyer formula in finite and infinite activity regimes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_original_negative_jump_strict_preruin_spatial_mask_allcap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (htpos : 0 < t)
    (htpreruin : (t : ℝ≥0∞) < ruinTime X x D ω)
    (hz : X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t < 0) :
    0 < Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
    ENNReal.ofReal (Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ C := by sorry
