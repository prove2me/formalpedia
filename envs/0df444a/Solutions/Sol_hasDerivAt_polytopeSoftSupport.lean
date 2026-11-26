-- Prove2me | solution 1 for hasDerivAt_polytopeSoftSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:07:46.258567+00:00
-- url     : https://prove2.me/submissions/511d76a8-34f4-4cbd-8413-be2a4d45275a

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Theorems.Thm_hasDerivAt_polytopeSoftPartition
import Theorems.Thm_polytopeSoftPartition_pos


set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) (delta theta : ℝ) :
    HasDerivAt (polytopeSoftSupport u delta)
      (polytopeSoftSupportFirst u delta theta) theta := by
  have hlog := (hasDerivAt_polytopeSoftPartition u delta theta).log
    (polytopeSoftPartition_pos hu delta theta).ne'
  have h := hlog.const_mul delta
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x => by
    rfl
