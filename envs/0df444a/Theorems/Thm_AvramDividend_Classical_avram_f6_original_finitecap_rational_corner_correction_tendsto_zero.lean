-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_finitecap_rational_corner_correction_tendsto_zero
-- name    : AvramDividend.Classical.avram_f6_original_finitecap_rational_corner_correction_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T18:38:56.518831+00:00
-- url     : https://prove2.me/theorems/1d3dc336-71ec-43a2-9d91-8191f3cebfb0
-- title:
--   Exact original finite-cap rational corner defect vanishes as cutoff approaches the cap
-- statement:
--   For the original finite positive cap C and continuous-on-positive candidate w, the source-exact caplinear terminal corner scalar correction (w(C)-w(b_j))-(C-b_j), where b_j=C.toReal*(j+1)/(j+2), tends to zero. This directly eliminates the deterministic finite-cap upper-corner error in the Gaussian stopped Itô/HJB source. Reuses an existing Proved generic scalar correction theorem and the Mathlib rational ratio limit.
-- source:
--   Proved avram_p3_grid4_finite_cap_corner_scalar_defect_tendsto_zero e9769c10 and pinned Mathlib tendsto_natCast_div_add_atTop.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_finitecap_rational_corner_correction_tendsto_zero
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0)) :
    Tendsto (fun j : ℕ =>
      (w C.toReal -
        w (C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))) -
      (C.toReal -
        C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))))
      atTop (𝓝 (0 : ℝ)) := by sorry
