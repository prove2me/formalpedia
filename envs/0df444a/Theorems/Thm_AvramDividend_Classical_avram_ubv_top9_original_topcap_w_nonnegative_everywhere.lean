-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_topcap_w_nonnegative_everywhere
-- name    : AvramDividend.Classical.avram_ubv_top9_original_topcap_w_nonnegative_everywhere
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:48:55.08741+00:00
-- url     : https://prove2.me/theorems/5224d9f0-0a52-45ab-a7b3-84ae065b2dcd
-- title:
--   Original infinite-cap HJB value is globally nonnegative
-- statement:
--   The original continuous HJB candidate, smooth and gradient-dominating on all positive reserves, and zero at every negative reserve, is nonnegative everywhere. This includes both the pre-ruin and post-ruin reserve conventions for stopped rewards.
-- source:
--   Authorised source-exact C2 and boundary conditions, plus accepted infinite-cap global gradient secant bb23d9ab.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_topcap_w_nonnegative_everywhere
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y : ℝ) : 0 ≤ w y := by sorry
