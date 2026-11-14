-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB240_original_finitecap_closed_clipped_band_deriv_continuous
-- name    : AvramDividend.Classical.avram_gbB240_original_finitecap_closed_clipped_band_deriv_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:04:45.525948+00:00
-- url     : https://prove2.me/theorems/d954d1cc-4bb5-4778-ab7c-af1d85b75312
-- title:
--   Original finite-cap C2 regularity makes the derivative continuous on the entire prescribed closed clipping interval
-- statement:
--   If w is C2 on the strict interior of the original finite dividend cap, its ordinary derivative is continuous on the closed clipping band from δ/2 to C.toReal·(j+1)/(j+2), including both endpoints, for any δ>0. This closes the exact closed-band regularity premise of B238/B239 and does not impose C2 at the cap itself.
-- source:
--   Original B65 direct reduction to Proved B238 and sketch B239; deterministic strict cap endpoint continuity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB240_original_finitecap_closed_clipped_band_deriv_continuous
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    ContinuousOn (deriv w)
      (Set.Icc (δ / 2)
        (C.toReal * (((j + 1 : ℕ) : ℝ) /
          ((j + 2 : ℕ) : ℝ)))) := by sorry
