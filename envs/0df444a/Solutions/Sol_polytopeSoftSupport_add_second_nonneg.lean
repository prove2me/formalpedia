-- Prove2me | solution 1 for polytopeSoftSupport_add_second_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:23:49.6328+00:00
-- url     : https://prove2.me/submissions/3b1dc840-092e-4501-a2eb-f0c0b3254b60

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Theorems.Thm_polytopeSoftPartitionSecond_eq_velocitySqMoment_sub_positionMoment
import Theorems.Thm_polytopeSoftPartitionPositionMoment_le_log_mul_partition
import Theorems.Thm_polytopeSoftPartitionFirst_sq_le_partition_mul_velocitySqMoment
import Theorems.Thm_polytopeSoftPartition_pos


set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta : ℝ} (hdelta : 0 < delta)
    (theta : ℝ) :
    0 ≤ polytopeSoftSupport u delta theta +
      polytopeSoftSupportSecond u delta theta := by
  let S := polytopeSoftPartition u delta theta
  let F := polytopeSoftPartitionFirst u delta theta
  let V := polytopeSoftPartitionVelocitySqMoment u delta theta
  let Q := polytopeSoftPartitionPositionMoment u delta theta
  have hS : 0 < S := polytopeSoftPartition_pos hu delta theta
  have hentropy : Q ≤ S * Real.log S := by
    exact polytopeSoftPartitionPositionMoment_le_log_mul_partition
      hu hdelta theta
  have hvariance : F ^ 2 ≤ S * V := by
    exact polytopeSoftPartitionFirst_sq_le_partition_mul_velocitySqMoment
      u delta theta
  have hentropyScaled : S * Q ≤ S * (S * Real.log S) :=
    mul_le_mul_of_nonneg_left hentropy hS.le
  have hnum :
      0 ≤ Real.log S * S ^ 2 + (V - Q) * S - F ^ 2 := by
    nlinarith only [hentropyScaled, hvariance]
  have hfrac :
      0 ≤ (Real.log S * S ^ 2 + (V - Q) * S - F ^ 2) / S ^ 2 :=
    div_nonneg hnum (sq_nonneg S)
  have hscaled := mul_nonneg hdelta.le hfrac
  unfold polytopeSoftSupport polytopeSoftSupportSecond
  rw [polytopeSoftPartitionSecond_eq_velocitySqMoment_sub_positionMoment]
  change 0 ≤ delta * Real.log S +
    delta * (((V - Q) * S - F ^ 2) / S ^ 2)
  have heq : delta * Real.log S +
        delta * (((V - Q) * S - F ^ 2) / S ^ 2) =
      delta *
        ((Real.log S * S ^ 2 + (V - Q) * S - F ^ 2) / S ^ 2) := by
    field_simp [hS.ne']
    ring
  rw [heq]
  exact hscaled
