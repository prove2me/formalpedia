-- Prove2me | solution 1 for natDegree_crouzeixProductRemainderPolynomial_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:37.77695+00:00
-- url     : https://prove2.me/submissions/5e760396-94de-4fb0-b03c-67f5fecfbb7c

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
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (ha : a ≠ 0) :
    (crouzeixProductRemainderPolynomial Omega (a • p)).natDegree =
      (crouzeixProductRemainderPolynomial Omega p).natDegree := by
  rw [crouzeixProductRemainderPolynomial_smul,
    Polynomial.natDegree_smul _ (mul_ne_zero (star_ne_zero.mpr ha) ha)]
