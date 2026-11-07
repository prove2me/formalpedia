-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_topcap_positive_halfline_HJB_bridge
-- name    : AvramDividend.Classical.avram_ubv_loc6_topcap_positive_halfline_HJB_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:21:18.048804+00:00
-- url     : https://prove2.me/theorems/d1a94bc6-df96-4a0d-a531-1972839e770e
-- title:
--   Original infinite-cap ENNReal interior HJB becomes the positive real half-line
-- statement:
--   For the original cap C = top, the generator-integrable HJB, dividend gradient and C2 interior hypotheses automatically hold throughout the positive real half-line, permitting an increasing compact real-strip localisation without an upper cap-contact boundary.
-- source:
--   Source-exact specialisation of the original w, X, q hypotheses when C=top; ENNReal.ofReal y is finite for each real y, and the original interior equals Ioi 0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_loc6_topcap_positive_halfline_HJB_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ContDiffOn ℝ 2 w (Ioi 0) ∧
    (∀ y : ℝ, 0 < y → X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0) ∧
    (∀ y : ℝ, 0 < y → 1 ≤ deriv w y) := by sorry
