-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger87_original_strict_rightlimit_le_later_dividend
-- name    : AvramDividend.Classical.avram_gledger87_original_strict_rightlimit_le_later_dividend
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:56:11.187203+00:00
-- url     : https://prove2.me/theorems/6e3bee4e-b6e2-43a9-9140-2a8f12fc78ee
-- title:
--   Original strict earlier dividend right limit is bounded by later actual dividend
-- statement:
--   For a genuine original admissible dividend strategy and strictly ordered times a<b, the right dividend limit immediately after a does not exceed the actual pre-rightpayment cumulative dividends at b, even if an instantaneous right payment occurs at b. This follows from monotone right limits and the identity between their left limit at b and D b.
-- source:
--   Genuine original strategy chronological ordering needed to instantiate the terminal gledger86 cancellation in the crossing cell of gledger81 16e988d7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gledger87_original_strict_rightlimit_le_later_dividend
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) (hab : a < b) :
    rightLimit D a ω ≤ D b ω := by sorry
