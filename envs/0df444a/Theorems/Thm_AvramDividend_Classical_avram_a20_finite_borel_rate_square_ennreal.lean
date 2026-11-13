-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_finite_borel_rate_square_ennreal
-- name    : AvramDividend.Classical.avram_a20_finite_borel_rate_square_ennreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:43:06.298204+00:00
-- url     : https://prove2.me/theorems/3967022e-8191-4cb5-9d1c-363d137f9cc2
-- title:
--   Exact finite Borel jump rate squared converts from real to ENNReal for any measure
-- statement:
--   For any measure on real marks with finite intensity on an arbitrary measurable mark set B and any nonnegative horizon T, the ENNReal of half the squared real source rate exactly equals half the square of the extended nonnegative product rate T μ(B). This extends a previously Proved fixed negative-cutoff Lévy measure conversion to arbitrary Borel source rates and supplies the final measure-theoretic conversion in the arbitrary physical chronological pair expectation limit.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a20_finite_borel_rate_square_ennreal
    (μ : Measure ℝ) (B : Set ℝ)
    (T : ℝ≥0) (hν : μ B < ⊤) :
    ENNReal.ofReal ((((T : ℝ) * (μ B).toReal) ^ 2) / 2) =
      (((T : ℝ≥0∞) * μ B) ^ 2) / 2 := by sorry
