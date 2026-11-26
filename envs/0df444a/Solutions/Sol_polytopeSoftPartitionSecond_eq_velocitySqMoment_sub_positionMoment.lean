-- Prove2me | solution 1 for polytopeSoftPartitionSecond_eq_velocitySqMoment_sub_positionMoment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:21:25.757637+00:00
-- url     : https://prove2.me/submissions/6b271410-4284-4ef5-b0df-367204dc36ed

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    (u : Finset ℂ) (delta theta : ℝ) :
    polytopeSoftPartitionSecond u delta theta =
      polytopeSoftPartitionVelocitySqMoment u delta theta -
        polytopeSoftPartitionPositionMoment u delta theta := by
  unfold polytopeSoftPartitionSecond
    polytopeSoftPartitionVelocitySqMoment
    polytopeSoftPartitionPositionMoment
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  ring
