-- Prove2me | solution 1 for norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_squareAux_add_remainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:53.817795+00:00
-- url     : https://prove2.me/submissions/9cd84888-cb08-4fb1-b790-945125db39be

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
import Theorems.Thm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_squareAux_sub_aeval_remainderPolynomial

set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      ‖crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p)‖ +
      ‖Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p)‖ := by
  rw [
    aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_squareAux_sub_aeval_remainderPolynomial
      A Omega p hOmega]
  exact norm_sub_le _ _
