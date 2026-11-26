-- Prove2me | solution 1 for norm_aeval_crouzeixProductRemainderPolynomial_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:22.278777+00:00
-- url     : https://prove2.me/submissions/a6cb70c7-6a51-490f-9a2c-806112af9abc

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
import Theorems.Thm_crouzeixProductRemainderPolynomial_smul

set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega (a • p))‖ =
      ‖a‖ ^ 2 *
        ‖Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p)‖ := by
  rw [crouzeixProductRemainderPolynomial_smul, map_smul, norm_smul,
    norm_mul, norm_star, pow_two]
