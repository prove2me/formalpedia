-- Prove2me | solution 1 for polytopeRoundedSupport_add_deriv_deriv_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:27:41.847417+00:00
-- url     : https://prove2.me/submissions/0f9f352b-90e9-4522-826b-631df57a82a8

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Theorems.Thm_polytopeSoftSupport_add_const_add_second_pos
import Theorems.Thm_deriv_deriv_polytopeRoundedSupport

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (theta : ℝ) :
    0 < polytopeRoundedSupport u delta rho theta +
      deriv (deriv (polytopeRoundedSupport u delta rho)) theta := by
  rw [deriv_deriv_polytopeRoundedSupport hu delta rho theta]
  exact polytopeSoftSupport_add_const_add_second_pos
    hu hdelta hrho theta
