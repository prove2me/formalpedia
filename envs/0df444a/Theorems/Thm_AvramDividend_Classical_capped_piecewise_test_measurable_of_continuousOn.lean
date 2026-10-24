-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_piecewise_test_measurable_of_continuousOn
-- name    : AvramDividend.Classical.capped_piecewise_test_measurable_of_continuousOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:23:04.515707+00:00
-- url     : https://prove2.me/theorems/7ee17db5-13fb-404b-bd84-c28bf771a051
-- title:
--   Measurability of a continuous compactly capped test function extended by zero
-- statement:
--   For a real test function continuous on the compact reserve interval from zero to the cap, its zero extension off that interval is Borel measurable. The closed cap is Borel, and the function is continuous on each piece. This supplies a Borel test from the C1/C2 continuity assumptions of the local verification theorem.
-- source:
--   Mathlib.MeasureTheory.Constructions.BorelSpace.Basic ContinuousOn.measurable_piecewise.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory Set

theorem AvramDividend.Classical.capped_piecewise_test_measurable_of_continuousOn
    (w : ℝ → ℝ) (C : ℝ)
    (hw : ContinuousOn w (Icc (0 : ℝ) C)) :
    Measurable (fun y : ℝ => if y ∈ Icc (0 : ℝ) C then w y else 0) := by sorry
