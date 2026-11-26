-- Prove2me | solution 1 for hasDerivAt_polytopeSoftPartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:05:06.144691+00:00
-- url     : https://prove2.me/submissions/5e5bb237-0aab-4839-9e7b-0cda8dc636ca

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Theorems.Thm_hasDerivAt_polytopeDirectionalValue
section
open Complex Set
open scoped ContDiff
private theorem hasDerivAt_polytopeSoftWeight
    (z : ℂ) (delta theta : ℝ) :
    HasDerivAt
      (fun x => Real.exp (polytopeDirectionalValue z x / delta))
      (Real.exp (polytopeDirectionalValue z theta / delta) *
        (polytopeDirectionalVelocity z theta / delta)) theta := by
  exact (Real.hasDerivAt_exp _).comp theta
    ((hasDerivAt_polytopeDirectionalValue z theta).div_const delta)
end

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    (u : Finset ℂ) (delta theta : ℝ) :
    HasDerivAt (polytopeSoftPartition u delta)
      (polytopeSoftPartitionFirst u delta theta) theta := by
  unfold polytopeSoftPartition polytopeSoftPartitionFirst
  have h := HasDerivAt.sum (u := u) fun z hz =>
    hasDerivAt_polytopeSoftWeight z delta theta
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x => by
    rw [Finset.sum_apply]
