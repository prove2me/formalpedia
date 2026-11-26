-- Prove2me | solution 1 for normalized_crouzeixProductRemainderContour_eq_aeval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:49.305025+00:00
-- url     : https://prove2.me/submissions/2db79175-f4ba-47ca-9265-11c4231dc595

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
import Theorems.Thm_contourIntegral_crouzeixProductRemainder_eq_sum
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral
          (fun z => star (Polynomial.eval z p) •
            Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
          Omega.boundaryParam =
      Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) := by
  rw [contourIntegral_crouzeixProductRemainder_eq_sum]
  unfold crouzeixProductRemainderPolynomial
  rw [map_sum]
  simp only [Finset.smul_sum, Polynomial.aeval_monomial,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul]
