-- Prove2me | solution 1 for norm_eval_add_C_star_sub_scalarCompanionClosedExtension_add_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:22:57.2739+00:00
-- url     : https://prove2.me/submissions/90f3e872-cde5-4bf6-9128-5263c82fe86e

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_add_C_of_isBounded

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (a : ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖Polynomial.eval z (q + Polynomial.C (star a)) -
        crouzeixPolynomialScalarCompanionClosedExtension
          Omega (p + Polynomial.C a) z‖ =
      ‖Polynomial.eval z q -
        crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ := by
  rw [Polynomial.eval_add, Polynomial.eval_C,
    crouzeixPolynomialScalarCompanionClosedExtension_add_C_of_isBounded
      Omega p a hbounded hkernel hz]
  congr 1
  ring
