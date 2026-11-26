-- Prove2me | solution 1 for crouzeixBoundaryPhaseContractive_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:14:30.55138+00:00
-- url     : https://prove2.me/submissions/c0288caa-dfb0-411c-8e6f-9f8d29618099

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_smul
import Theorems.Thm_polynomialSupNorm_smul


set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
theorem _root_.solution
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ)
    (hp : CrouzeixBoundaryPhaseContractive Omega p) :
    CrouzeixBoundaryPhaseContractive Omega (a • p) := by
  intro xi hxi
  have hpbound :
      ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤
        polynomialSupNorm p (frontier Omega.carrier) := by
    rw [
      crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform]
    exact hp xi hxi
  rw [←
    crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform,
    crouzeixPolynomialScalarCompanionBoundaryValue_smul,
    norm_mul, norm_star, polynomialSupNorm_smul]
  exact mul_le_mul_of_nonneg_left hpbound (norm_nonneg a)
