-- Prove2me | solution 1 for crouzeixPolynomialAuxiliaryOperator_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:33.663801+00:00
-- url     : https://prove2.me/submissions/8b6f8ed8-6650-4bfd-b0be-ce30ee9fe047

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Theorems.Thm_contourIntegral_add
import Theorems.Thm_crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable


set_option autoImplicit false
open Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
theorem _root_.solution
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (p q : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    crouzeixPolynomialAuxiliaryOperator A Omega (p + q) =
      crouzeixPolynomialAuxiliaryOperator A Omega p +
        crouzeixPolynomialAuxiliaryOperator A Omega q := by
  unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
  have hfun :
      (fun z => star (Polynomial.eval z (p + q)) • resolvent A z) =
        fun z =>
          (star (Polynomial.eval z p) • resolvent A z) +
            (star (Polynomial.eval z q) • resolvent A z) := by
    funext z
    rw [Polynomial.eval_add, star_add, add_smul]
  rw [hfun, contourIntegral_add
    (crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable A Omega p hOmega)
    (crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable A Omega q hOmega),
    smul_add]
