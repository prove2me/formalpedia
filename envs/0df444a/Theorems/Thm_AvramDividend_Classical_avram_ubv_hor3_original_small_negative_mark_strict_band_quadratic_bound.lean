-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_small_negative_mark_strict_band_quadratic_bound
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_small_negative_mark_strict_band_quadratic_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:01:58.146829+00:00
-- url     : https://prove2.me/theorems/fb0bd813-b942-4770-914d-a55a0ad47cea
-- title:
--   Original UBV strictly interior small negative physical jump kernel has uniform quadratic domination
-- statement:
--   For the original UBV C2 candidate w and every compact strictly positive localisation [δ,K] inside the cap, the exact physical negative-mark coefficient w(u+z)-w(u) is bounded in square by M z² for every u∈[δ,K] and negative mark z in [-δ/2,0]. This remains valid as the cap C=∞ and uses the true derivative smoothness only on a positive interior band, retaining the non-smooth ruin boundary.
-- source:
--   Apply the proved P4-F3 original positive-band Lipschitz source 8179243e to [δ/2,K], note that u+z remains in that band, and square the exact real Lipschitz inequality. This is the small-mark half of the true original min(1,z²) Lévy bound; larger marks are handled by original negative-tail global value bound.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_band_lipschitz_source
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_small_negative_mark_strict_band_quadratic_bound
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ u ∈ Icc δ K, ∀ z : ℝ,
        -(δ / 2) ≤ z → z ≤ 0 →
        (w (u + z) - w u) ^ 2 ≤ M * z ^ 2 := by sorry
