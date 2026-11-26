-- Prove2me | solution 1 for polytopeSoftSupport_add_const_add_second_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:26:23.843226+00:00
-- url     : https://prove2.me/submissions/78ea5c3a-cd86-40fa-9cbb-a29ce49f44cf

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Theorems.Thm_polytopeSoftSupport_add_second_nonneg

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (theta : ℝ) :
    0 < (polytopeSoftSupport u delta theta + rho) +
      polytopeSoftSupportSecond u delta theta := by
  have hbase := polytopeSoftSupport_add_second_nonneg hu hdelta theta
  linarith
