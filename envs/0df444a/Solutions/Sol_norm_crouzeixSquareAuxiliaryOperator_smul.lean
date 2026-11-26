-- Prove2me | solution 1 for norm_crouzeixSquareAuxiliaryOperator_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:43.432296+00:00
-- url     : https://prove2.me/submissions/e4e1ce03-2107-44e6-b52b-f0789b557ba0

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
import Theorems.Thm_crouzeixSquareAuxiliaryOperator_smul

set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    ‖crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z (a • p)) * Polynomial.eval z (a • p))‖ =
      ‖a‖ ^ 2 * ‖crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p)‖ := by
  rw [crouzeixSquareAuxiliaryOperator_smul, norm_smul, norm_mul, norm_star, pow_two]
