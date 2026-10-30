-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_lower_clock_strict_preclock_closed_survival
-- name    : AvramDividend.Classical.avram_ws01b_lower_clock_strict_preclock_closed_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:37:39.083747+00:00
-- url     : https://prove2.me/theorems/98c4d827-5827-4204-8280-8c9c5be8ac5c
-- title:
--   Actual strict pre-ruin sampling clocks preserve full closed-path survival
-- statement:
--   For the actual original spectrally negative Levy path, if a bounded observation time is strictly before the true strict lower passage clock, its complete closed history remains nonnegative at every earlier real time. This is the sample-path premise ensuring the continuously killed martingale's full-history indicator equals one along sufficiently fine stopped grids on the upper-first event.
-- source:
--   Exact source twoSidedExitDownTime as an extended real infimum of strict negative observations. Any negative reserve before or at t supplies a witness giving passage time at most t, contradicting t strictly earlier than lower passage; the closed endpoint is retained.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_lower_clock_strict_preclock_closed_survival
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω) :
    ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω := by sorry
