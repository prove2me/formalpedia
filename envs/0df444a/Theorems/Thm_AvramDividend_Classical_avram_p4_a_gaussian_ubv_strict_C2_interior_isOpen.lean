-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:58:45.671399+00:00
-- url     : https://prove2.me/theorems/b917eaf2-3077-447f-bbe3-ab4d12ed22a8
-- title:
--   The exact positive below-cap C2 interior is open for every source cap
-- statement:
--   For every extended nonnegative source cap C, the exact strict interior 0<y and ENNReal.ofReal y<C used in Proposition 4(i) is open. The proof uses the pinned continuous real-to-ENNReal embedding and preimages of open order intervals. No continuity through ruin or the cap is assumed, and the statement remains valid for C=0 and C=top.
-- source:
--   Avram Palmowski Pistorius Proposition 4(i) strict open interior, pinned Mathlib ENNReal.continuous_ofReal and open order interval preimage.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen
    (C : ℝ≥0∞) :
    IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by sorry
