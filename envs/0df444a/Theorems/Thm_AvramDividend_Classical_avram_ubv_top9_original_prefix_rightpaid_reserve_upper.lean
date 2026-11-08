-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_prefix_rightpaid_reserve_upper
-- name    : AvramDividend.Classical.avram_ubv_top9_original_prefix_rightpaid_reserve_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:20:55.925208+00:00
-- url     : https://prove2.me/theorems/2036a555-db70-4784-a6f0-fc61018c772d
-- title:
--   Original prefix-bounded Lévy process bounds the ruin-sensitive post-rightpayment reserve
-- statement:
--   An admissible cumulative nondecreasing dividend process starting at zero gives nonnegative paid mass and nonnegative right limit. Under an original-path Levy prefix ceiling, both pre-ruin post-rightpayment and ruin-contact source reserve branches lie below initial reserve plus the prefix ceiling. This is the source-exact spatial bound needed by infinite-cap terminal envelope without a finite global cap.
-- source:
--   Literal original-process H_j terminal branch in 25573e81 and previous Proved dividendStrategy_path_nonneg; source-exact logical bridge into Proved e225ab08 terminal envelope.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_prefix_rightpaid_reserve_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (κ : Ω → ℝ≥0) (B : ℝ)
    (hXprefix : ∀ ω (t : ℝ≥0), t ≤ κ ω → X.X t ω ≤ B) :
    ∀ ω,
      (if κ ω = 0 ∨ (κ ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (κ ω) ω - rightLimit D (κ ω) ω
        else riskProcess X x D (κ ω) ω) ≤ x + B := by sorry
