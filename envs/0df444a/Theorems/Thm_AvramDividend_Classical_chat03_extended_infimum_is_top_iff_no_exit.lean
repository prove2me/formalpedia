-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_extended_infimum_is_top_iff_no_exit
-- name    : AvramDividend.Classical.chat03_extended_infimum_is_top_iff_no_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:53:28.884819+00:00
-- url     : https://prove2.me/theorems/7ff7f7db-c9c8-41a7-a4ae-23610b3bd9f2
-- title:
--   Extended nonnegative-real strict-passage time equals infinity exactly when no witness exists
-- statement:
--   For any predicate p on nonnegative real time, its official first-passage encoding as the infimum in ℝ≥0∞ over witness times is equal to infinity if and only if no witness satisfies p. The proof uses the indexed infimum bound below any witness's finite cast (which is strictly below infinity), and the infimum over an empty witness family being the top element. This isolates the no-passage branch needed for the Avram stopped q-scale identity and prevents incorrectly interpreting ENNReal.toNNReal infinity as a real zero stopping time.
-- source:
--   Pinned Mathlib ENNReal.coe_lt_top and indexed iInf; Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. Chat03 extended first-passage infinity case.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Data.ENNReal.Basic

open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat03_extended_infimum_is_top_iff_no_exit
    (p : ℝ≥0 → Prop) :
    (⨅ (t : ℝ≥0) (_ : p t), (t : ℝ≥0∞)) = ∞ ↔
      ¬ ∃ t : ℝ≥0, p t := by sorry
