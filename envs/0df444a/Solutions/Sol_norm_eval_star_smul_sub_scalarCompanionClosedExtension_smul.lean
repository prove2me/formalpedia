-- Prove2me | solution 1 for norm_eval_star_smul_sub_scalarCompanionClosedExtension_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:17.338616+00:00
-- url     : https://prove2.me/submissions/0d4b2130-1385-44d1-9c3e-63937bf5cf8a

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_smul_of_isBounded

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (a : ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖Polynomial.eval z ((star a) • q) -
        crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p) z‖ =
      ‖a‖ *
        ‖Polynomial.eval z q -
          crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ := by
  rw [Polynomial.eval_smul, smul_eq_mul,
    crouzeixPolynomialScalarCompanionClosedExtension_smul_of_isBounded
      Omega a p (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel hz,
    ← mul_sub, norm_mul, norm_star]
