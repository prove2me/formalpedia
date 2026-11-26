-- Prove2me | solution 1 for crouzeix_palencia_of_smoothJordanOuterApproximation_polytope_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:41:05.474409+00:00
-- url     : https://prove2.me/submissions/bc5bd01d-6eac-4615-a441-49e3bf274b4e

import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximationReduction
import Mathlib.Analysis.Normed.Affine.Convex
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Theorems.Thm_hasSmoothJordanOuterApproximation_of_polytope_case
import Theorems.Thm_crouzeix_palencia_of_smoothJordanOuterApproximation_nonemptyInterior_case


set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]
theorem _root_.solution
    (A : E →L[ℂ] E)
    (hpoly : HasSmoothJordanOuterApproximationForPolytopes) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_smoothJordanOuterApproximation_nonemptyInterior_case A
  intro K hKcompact hKconvex hKinterior
  exact hasSmoothJordanOuterApproximation_of_polytope_case
    hKcompact (hKinterior.mono interior_subset) hKconvex hpoly
