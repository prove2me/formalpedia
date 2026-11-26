-- Prove2me | solution 1 for hasDerivAt_polytopeSoftSupportFirst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:23:04.391638+00:00
-- url     : https://prove2.me/submissions/b4ab28e2-3bae-43c1-960e-38ccf09aa481

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Theorems.Thm_hasDerivAt_polytopeSoftPartition
import Theorems.Thm_hasDerivAt_polytopeSoftPartitionFirst
import Theorems.Thm_polytopeSoftPartition_pos


set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) (delta theta : ℝ) :
    HasDerivAt (polytopeSoftSupportFirst u delta)
      (polytopeSoftSupportSecond u delta theta) theta := by
  have hquot := (hasDerivAt_polytopeSoftPartitionFirst u delta theta).div
    (hasDerivAt_polytopeSoftPartition u delta theta)
    (polytopeSoftPartition_pos hu delta theta).ne'
  have h := hquot.const_mul delta
  have hcoef : delta *
      ((polytopeSoftPartitionSecond u delta theta *
            polytopeSoftPartition u delta theta -
          polytopeSoftPartitionFirst u delta theta *
            polytopeSoftPartitionFirst u delta theta) /
        polytopeSoftPartition u delta theta ^ 2) =
      polytopeSoftSupportSecond u delta theta := by
    unfold polytopeSoftSupportSecond
    ring
  rw [hcoef] at h
  apply h.congr_of_eventuallyEq
    (f₁ := polytopeSoftSupportFirst u delta)
  exact Filter.Eventually.of_forall fun x => by
    rfl
