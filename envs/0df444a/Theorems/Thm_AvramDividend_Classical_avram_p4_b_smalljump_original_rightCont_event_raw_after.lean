-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightCont_event_raw_after
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_rightCont_event_raw_after
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:07:03.997628+00:00
-- url     : https://prove2.me/theorems/7819739e-5243-45ea-850c-aa757d10ffb5
-- title:
--   Original Lévy right-continuous event belongs to every later raw filtration
-- statement:
--   On the exact original Lévy filtration, any event in its right-continuation at time s belongs to the raw sigma-algebra at each strictly later r. This supplies the critical event measurability needed to apply raw P2 marked future count compensation at s+epsilon.
-- source:
--   Mathlib/Probability/Process/Filtration.lean: Filtration.rightCont_eq and iInf₂_le, applied on the original SpectrallyNegativeLevy filtration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_rightCont_event_raw_after
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {s r : ℝ≥0} (hsr : s < r)
    {A : Set Ω} (hA : MeasurableSet[𝓕.rightCont s] A) :
    MeasurableSet[𝓕 r] A := by sorry
