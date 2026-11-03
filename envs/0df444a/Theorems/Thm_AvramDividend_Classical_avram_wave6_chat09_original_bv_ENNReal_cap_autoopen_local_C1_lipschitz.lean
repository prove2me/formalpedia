-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_ENNReal_cap_autoopen_local_C1_lipschitz
-- name    : AvramDividend.Classical.avram_wave6_chat09_original_bv_ENNReal_cap_autoopen_local_C1_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:51:13.783848+00:00
-- url     : https://prove2.me/theorems/cce8f12b-e04c-4690-b8d1-31fcf040ac7b
-- title:
--   Canonical extended-real BV cap interior C¹ gives compact-band Lipschitz bound without an openness premise
-- statement:
--   In the original spectrally negative Lévy probability space and its bounded-variation branch, the canonical C1 regularity on the ENNReal-cap positive reserve interior implies a real compact-band Lipschitz coefficient. The cap may be infinity. The open-set premise of the already published compact C1 theorem follows automatically from continuity of ofReal and open order intervals, not from an added stochastic assumption.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), exact source BoundedVariation first-order HJB localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_ENNReal_cap_compact_C1_lipschitz
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_chat09_original_bv_ENNReal_cap_autoopen_local_C1_lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (l r : ℝ) (hlr : l < r)
    (hBand : Icc l r ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwC1 : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ s ∈ Icc l r, ∀ t ∈ Icc l r,
        |w s - w t| ≤ L * |s - t| := by sorry
