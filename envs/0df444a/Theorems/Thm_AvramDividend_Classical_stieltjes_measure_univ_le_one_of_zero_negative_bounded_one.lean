-- Prove2me | Theorems.Thm_AvramDividend_Classical_stieltjes_measure_univ_le_one_of_zero_negative_bounded_one
-- name    : AvramDividend.Classical.stieltjes_measure_univ_le_one_of_zero_negative_bounded_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:57:09.567755+00:00
-- url     : https://prove2.me/theorems/7f8074c3-cfbf-445c-9a88-f9a0475e9d49
-- title:
--   A bounded Stieltjes distribution zero on negative reserves has total mass at most one
-- statement:
--   If a right-continuous monotone real Stieltjes distribution vanishes on every negative argument and stays bounded by one, then its associated positive measure has total mass no more than one. The Stieltjes measure can be defective and need not be normalised as a probability measure.
-- source:
--   Use eventual equality at negative infinity for the lower limit zero; use pinned `tendsto_atTop_ciSup S.mono` and `iSup_le` for the bounded upper limit. Then apply pinned `StieltjesFunction.measure_univ` to express total mass as the limit gap and bound the ENNReal mass.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.Filter.AtTopBot.Defs
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.stieltjes_measure_univ_le_one_of_zero_negative_bounded_one
    (S : StieltjesFunction ℝ)
    (hneg : ∀ x : ℝ, x < 0 → S x = 0)
    (hbound : ∀ x : ℝ, S x ≤ 1) :
    S.measure Set.univ ≤ 1 := by sorry
