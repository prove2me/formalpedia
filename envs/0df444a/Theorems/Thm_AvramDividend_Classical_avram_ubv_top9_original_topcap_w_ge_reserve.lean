-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_topcap_w_ge_reserve
-- name    : AvramDividend.Classical.avram_ubv_top9_original_topcap_w_ge_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:54:11.031051+00:00
-- url     : https://prove2.me/theorems/85dde53e-3c6a-446c-b31b-e56b593e4880
-- title:
--   Infinite-cap HJB candidate dominates every nonnegative reserve
-- statement:
--   Under the exact original infinite-cap generator-test smoothness, derivative-lower-bound, half-line continuity and nonnegative origin value, the candidate function dominates every nonnegative reserve. This includes the zero boundary, without differentiating at the zero reserve.
-- source:
--   Original topcap C2 to C1 restriction and public accepted infinite-cap global gradient secant bb23d9ab; analytically supports 25573e81 and 148b2516.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_topcap_w_ge_reserve
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y : ℝ) (hy : 0 ≤ y) :
    y ≤ w y := by sorry
