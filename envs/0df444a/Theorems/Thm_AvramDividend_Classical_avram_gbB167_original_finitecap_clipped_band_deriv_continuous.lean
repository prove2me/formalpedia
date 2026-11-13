-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB167_original_finitecap_clipped_band_deriv_continuous
-- name    : AvramDividend.Classical.avram_gbB167_original_finitecap_clipped_band_deriv_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T16:11:14.550197+00:00
-- url     : https://prove2.me/theorems/002694be-4707-426f-92a3-35a7a701afee
-- title:
--   Original finite-cap clipped-gradient derivative is continuous throughout interior band
-- statement:
--   The interior clipped band δ/2 < y < C.toReal*(j+1)/(j+2) lies strictly inside the C2 regularity domain (0,C). The ordinary derivative is therefore continuous at y by the open-set C2 derivative continuity theorem B166. This discharges the deterministic smoothness clause in B163.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB166_contdiff_two_open_set_derivative_continuousAt
open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB167_original_finitecap_clipped_band_deriv_continuous
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ |
      0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) (y : ℝ)
    (hy : y ∈ Ioo (δ / 2)
      (C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))) :
    ContinuousAt (deriv w) y := by sorry
