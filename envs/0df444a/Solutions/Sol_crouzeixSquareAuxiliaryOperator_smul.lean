-- Prove2me | solution 1 for crouzeixSquareAuxiliaryOperator_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:28.483248+00:00
-- url     : https://prove2.me/submissions/7a3eccc4-0dca-4cd6-a6bc-88eaa166fe44

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
import Theorems.Thm_crouzeixAuxiliaryOperator_smul
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z (a • p)) * Polynomial.eval z (a • p)) =
      (star a * a) • crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) := by
  have hfun :
      (fun z => star (Polynomial.eval z (a • p)) * Polynomial.eval z (a • p)) =
      fun z => (star a * a) •
        (star (Polynomial.eval z p) * Polynomial.eval z p) := by
    funext z
    rw [Polynomial.eval_smul]
    simp only [smul_eq_mul, star_mul]
    ring
  rw [hfun, crouzeixAuxiliaryOperator_smul]
