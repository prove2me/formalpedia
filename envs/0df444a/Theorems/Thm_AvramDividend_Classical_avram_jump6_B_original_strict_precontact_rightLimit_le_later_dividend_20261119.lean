-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_strict_precontact_rightLimit_le_later_dividend_20261119
-- name    : AvramDividend.Classical.avram_jump6_B_original_strict_precontact_rightLimit_le_later_dividend_20261119
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:26:46.825319+00:00
-- url     : https://prove2.me/theorems/54a5c1f8-a226-4ebb-8bd2-478043474444
-- title:
--   Original admissible dividend right-limit before a strictly later payment
-- statement:
--   The original dividend strategy is nondecreasing, so its right-limit at any strictly earlier time is no greater than its later value. This supports the original crossing-cell signed cash inequality without a finite-activity assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys119_original_dividend_rightLimit_eq_strict_rightLim
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_realTime_monotone
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_strict_precontact_rightLimit_le_later_dividend_20261119
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hDstrat : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a ρ : ℝ≥0) (h : a < ρ) :
    rightLimit D a ω ≤ D ρ ω := by sorry
