-- Prove2me | solution 1 for polytopeSoftPartitionFirst_sq_le_partition_mul_velocitySqMoment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:22:37.287963+00:00
-- url     : https://prove2.me/submissions/4309d722-b347-425b-b2c1-b77971bcc559

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    (u : Finset ℂ) (delta theta : ℝ) :
    polytopeSoftPartitionFirst u delta theta ^ 2 ≤
      polytopeSoftPartition u delta theta *
        polytopeSoftPartitionVelocitySqMoment u delta theta := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (R := ℝ) u
    (r := fun z => Real.exp (polytopeDirectionalValue z theta / delta) *
      (polytopeDirectionalVelocity z theta / delta))
    (f := fun z => Real.exp (polytopeDirectionalValue z theta / delta))
    (g := fun z => Real.exp (polytopeDirectionalValue z theta / delta) *
      (polytopeDirectionalVelocity z theta / delta) ^ 2)
    (fun z hz => (Real.exp_pos _).le)
    (fun z hz => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    (fun z hz => by
      ring_nf
      exact le_rfl)
  exact hcs
