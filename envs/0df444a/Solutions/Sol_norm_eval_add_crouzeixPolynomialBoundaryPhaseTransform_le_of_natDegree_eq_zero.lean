-- Prove2me | solution 1 for norm_eval_add_crouzeixPolynomialBoundaryPhaseTransform_le_of_natDegree_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:31.5181+00:00
-- url     : https://prove2.me/submissions/7592ff7f-067b-4c3f-b3d6-818c4c6fa523

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_polynomialSupNorm_C_of_nonempty
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange


attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero

set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hp : p.natDegree = 0) (xi : ℂ) :
    ‖star (Polynomial.eval xi p) +
        crouzeixPolynomialBoundaryPhaseTransform Omega xi
          (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
      polynomialSupNorm p (frontier Omega.carrier) := by
  have hfrontier : (frontier Omega.carrier).Nonempty := by
    refine ⟨Omega.boundaryParam 0, ?_⟩
    rw [← Omega.boundaryParam_range]
    exact mem_range_self 0
  rw [Polynomial.eq_C_of_natDegree_eq_zero hp]
  have hdiv :
      Polynomial.C (p.coeff 0) /ₘ
          (Polynomial.X - Polynomial.C xi) = 0 := by
    apply (Polynomial.divByMonic_eq_zero_iff
      (Polynomial.monic_X_sub_C xi)).2
    rw [Polynomial.degree_X_sub_C]
    exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
  rw [hdiv, crouzeixPolynomialBoundaryPhaseTransform_zero,
    add_zero, Polynomial.eval_C, norm_star,
    polynomialSupNorm_C_of_nonempty _ hfrontier]
