-- Prove2me | solution 1 for crouzeixProductRemainderPolynomial_eq_zero_of_natDegree_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:49.954973+00:00
-- url     : https://prove2.me/submissions/9e77d7ac-adba-4483-8fce-50c92358a450

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (hp : p.natDegree = 0) :
    crouzeixProductRemainderPolynomial Omega p = 0 := by
  simp only [crouzeixProductRemainderPolynomial, hp, Finset.range_zero, Finset.sum_empty]
