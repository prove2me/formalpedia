-- Prove2me | solution 1 for polynomialSupNorm_crouzeixProductRemainderPolynomial_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:26.721996+00:00
-- url     : https://prove2.me/submissions/99e60abf-fe08-4137-9708-2b423855b7f8

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
import Theorems.Thm_crouzeixProductRemainderPolynomial_smul
import Theorems.Thm_polynomialSupNorm_smul


set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (K : Set ℂ) :
    polynomialSupNorm (crouzeixProductRemainderPolynomial Omega (a • p)) K =
      ‖a‖ ^ 2 * polynomialSupNorm (crouzeixProductRemainderPolynomial Omega p) K := by
  rw [crouzeixProductRemainderPolynomial_smul, polynomialSupNorm_smul,
    norm_mul, norm_star, pow_two]
