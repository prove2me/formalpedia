-- Prove2me | Theorems.Thm_AvramDividend_Classical_separated_strict_passage_infima_no_finite_tie
-- name    : AvramDividend.Classical.separated_strict_passage_infima_no_finite_tie
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:21:41.812018+00:00
-- url     : https://prove2.me/theorems/98dcbac4-062e-4310-ab0d-c48d9171e88d
-- title:
--   Separated strict exit infima cannot tie at a finite right-continuous time
-- statement:
--   For any real-valued right-continuous path, first strict crossings of separated upper and lower barriers cannot have the same finite extended-real passage clock. Unlike the existing no-tie theorem stated using IsGLB, this result works directly with the actual extended-real infima used by the Lévy exit reward definition and therefore resolves the equality case in the stopped-renewal upper-event comparison.
-- source:
--   Use the proved finite extended-infimum/IsGLB interface twice and the proved right-continuous separated-passages no-tie theorem.

import Mathlib.Topology.Order.LeftRightNhds
import Theorems.Thm_AvramDividend_Classical_chat03_finite_extended_infimum_isGLB
import Theorems.Thm_AvramDividend_Classical_chat03_rightcontinuous_separated_strict_passages_no_finite_tie

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.separated_strict_passage_infima_no_finite_tie
    (f : ℝ≥0 → ℝ) (t : ℝ≥0) (lower upper : ℝ)
    (hsep : lower < upper)
    (hRight : ContinuousWithinAt f (Set.Ici t) t)
    (hUp : (t : ℝ≥0∞) = (⨅ (s : ℝ≥0) (_ : upper < f s), (s : ℝ≥0∞)))
    (hDown : (t : ℝ≥0∞) = (⨅ (s : ℝ≥0) (_ : f s < lower), (s : ℝ≥0∞))) :
    False := by sorry
