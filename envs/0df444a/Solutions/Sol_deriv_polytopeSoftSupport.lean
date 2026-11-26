-- Prove2me | solution 1 for deriv_polytopeSoftSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:17:19.6259+00:00
-- url     : https://prove2.me/submissions/e8c7f387-12f2-49f5-a3b5-33f3e3b1b8d0

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Theorems.Thm_hasDerivAt_polytopeSoftSupport

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) (delta theta : ℝ) :
    deriv (polytopeSoftSupport u delta) theta =
      polytopeSoftSupportFirst u delta theta :=
  (hasDerivAt_polytopeSoftSupport hu delta theta).deriv
