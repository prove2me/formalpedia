-- Prove2me | solution 1 for norm_eval_star_smul_add_C_star_sub_scalarCompanionClosedExtension_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:24:11.203895+00:00
-- url     : https://prove2.me/submissions/0015d99a-e44b-4278-89b3-936dfe214fff

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_norm_eval_add_C_star_sub_scalarCompanionClosedExtension_add_C
import Theorems.Thm_norm_eval_star_smul_sub_scalarCompanionClosedExtension_smul

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (a b : ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖Polynomial.eval z ((star a) • q + Polynomial.C (star b)) -
        crouzeixPolynomialScalarCompanionClosedExtension
          Omega (a • p + Polynomial.C b) z‖ =
      ‖a‖ *
        ‖Polynomial.eval z q -
          crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ := by
  rw [norm_eval_add_C_star_sub_scalarCompanionClosedExtension_add_C
      Omega (a • p) ((star a) • q) b
        (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel) hkernel hz,
    norm_eval_star_smul_sub_scalarCompanionClosedExtension_smul
      Omega p q a hkernel hz]
