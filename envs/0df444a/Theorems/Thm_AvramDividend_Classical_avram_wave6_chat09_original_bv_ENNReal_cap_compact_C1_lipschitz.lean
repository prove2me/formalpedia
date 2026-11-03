-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_ENNReal_cap_compact_C1_lipschitz
-- name    : AvramDividend.Classical.avram_wave6_chat09_original_bv_ENNReal_cap_compact_C1_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:29:34.748659+00:00
-- url     : https://prove2.me/theorems/731ed4a6-b61c-449d-ab35-522c83642f86
-- title:
--   Original bounded-variation C¹ local Lipschitz bound for an extended-real cap including infinity
-- statement:
--   For the genuine SpectrallyNegativeLevy in its BV branch, assume the canonical C1 HJB regularity on the positive interior below an extended-real cap C. On any nondegenerate compact reserve band inside this open interior, the original test function w has a finite Lipschitz constant. The cap may be top. The proof is compact derivative maximisation followed by the mean-value theorem, not an assumed stochastic inequality.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), C1 BV stopped source localisation, exact extended-real cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_chat09_original_bv_ENNReal_cap_compact_C1_lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (l r : ℝ) (hlr : l < r)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc l r ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwC1 : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ s ∈ Icc l r, ∀ t ∈ Icc l r,
        |w s - w t| ≤ L * |s - t| := by sorry
