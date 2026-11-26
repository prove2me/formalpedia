-- Prove2me | solution 1 for deriv_deriv_polytopeRoundedSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:24:17.662314+00:00
-- url     : https://prove2.me/submissions/d820b95f-0dd7-4657-83c0-f1bc944efe86

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Theorems.Thm_hasDerivAt_polytopeSoftSupport
import Theorems.Thm_hasDerivAt_polytopeSoftSupportFirst

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) (delta rho theta : ℝ) :
    deriv (deriv (polytopeRoundedSupport u delta rho)) theta =
      polytopeSoftSupportSecond u delta theta := by
  have hfirst : deriv (polytopeRoundedSupport u delta rho) =
      polytopeSoftSupportFirst u delta := by
    funext x
    unfold polytopeRoundedSupport
    exact ((hasDerivAt_polytopeSoftSupport hu delta x).add_const rho).deriv
  rw [hfirst]
  exact (hasDerivAt_polytopeSoftSupportFirst hu delta theta).deriv
