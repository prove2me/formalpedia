-- Prove2me | solution 1 for kyprianou82_discountedAt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:34:17.372825+00:00
-- url     : https://prove2.me/submissions/c9072ca8-b8a8-427f-8b51-b01517679fcf

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    (q : ℝ) (hq : 0 ≤ q) (τ : WithTop ℝ≥0) : 0 ≤ discountedAt q τ := by
  cases τ using WithTop.recTopCoe with
  | top => simp [discountedAt]
  | coe t => simp [discountedAt]; positivity
