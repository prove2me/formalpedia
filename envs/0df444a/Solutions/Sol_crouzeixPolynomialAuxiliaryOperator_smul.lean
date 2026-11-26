-- Prove2me | solution 1 for crouzeixPolynomialAuxiliaryOperator_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:37:28.086744+00:00
-- url     : https://prove2.me/submissions/644bd747-16a2-4dbd-8439-2386d29dddf9

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Theorems.Thm_contourIntegral_smul
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem _root_.solution
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    crouzeixPolynomialAuxiliaryOperator A Omega (a • p) =
      star a • crouzeixPolynomialAuxiliaryOperator A Omega p := by
  unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
  have hfun :
      (fun z => star (Polynomial.eval z (a • p)) • resolvent A z) =
        fun z => star a • (star (Polynomial.eval z p) • resolvent A z) := by
    funext z
    rw [Polynomial.eval_smul, smul_eq_mul, star_mul, mul_comm, smul_smul]
  rw [hfun, contourIntegral_smul]
  simp only [smul_smul]
  rw [mul_comm (2 * (Real.pi : ℂ) * Complex.I)⁻¹ (star a)]
