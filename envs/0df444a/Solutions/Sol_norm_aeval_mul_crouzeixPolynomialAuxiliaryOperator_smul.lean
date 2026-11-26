-- Prove2me | solution 1 for norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:02.340807+00:00
-- url     : https://prove2.me/submissions/bbfd4f1d-efc6-4e6a-8d3d-028e0543d3b0

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Theorems.Thm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul

set_option autoImplicit false
open Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
omit [CompleteSpace H]
theorem _root_.solution
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A (a • p) *
        crouzeixPolynomialAuxiliaryOperator A Omega (a • p)‖ =
      ‖a‖ ^ 2 *
        ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ := by
  rw [aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul]
  rw [norm_smul, norm_mul, norm_star, pow_two]
