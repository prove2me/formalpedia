-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_weight_nat_caps_measurable
-- name    : AvramDividend.Classical.killed_weight_nat_caps_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:24:22.522267+00:00
-- url     : https://prove2.me/theorems/2e5ae04b-b127-47f0-82aa-102c67da66d4
-- title:
--   Finite-horizon killed rewards are measurable when passage clocks and rewards are measurable
-- statement:
--   The finite-horizon truncation of a measurable extended-valued reward by the event that a measurable passage clock is at most n is measurable. This supplies the measurability hypotheses for monotone convergence of killed-record integrals.
-- source:
--   Measurable.ite and measurableSet_le from pinned Mathlib

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.ENNReal.Basic

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_weight_nat_caps_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (T : Ω → ℝ≥0∞) (hT : Measurable T)
    (weight : Ω → ℝ≥0∞) (hw : Measurable weight) :
    ∀ n : ℕ, Measurable (fun ω : Ω =>
      if T ω ≤ (n : ℝ≥0∞) then weight ω else 0) := by sorry
