-- Prove2me | solution 1 for crouzeixAuxiliaryOperator_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:36.862317+00:00
-- url     : https://prove2.me/submissions/caa76101-ed17-4eea-8e7b-894da807c0d9

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
import Theorems.Thm_contourIntegral_smul
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (a : ℂ) (h : ℂ → ℂ) :
    crouzeixAuxiliaryOperator A Omega (fun z => a • h z) =
      a • crouzeixAuxiliaryOperator A Omega h := by
  unfold crouzeixAuxiliaryOperator
  have hfun :
      (fun z => (a • h z) • resolvent A z) =
        fun z => a • (h z • resolvent A z) := by
    funext z
    simp only [smul_eq_mul, smul_smul]
  rw [hfun, contourIntegral_smul]
  simp only [smul_smul]
  rw [mul_comm (2 * (Real.pi : ℂ) * Complex.I)⁻¹ a]
