-- Prove2me | solution 1 for ofReal_crouzeixBoundaryDoubleLayerDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:00.232853+00:00
-- url     : https://prove2.me/submissions/e7afa8f2-0859-4e3d-a6df-3bc4320053f8

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure

set_option autoImplicit false
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (xi : ℂ) (t : ℝ) :
    (crouzeixBoundaryDoubleLayerDensity Omega xi t : ℂ) =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (deriv Omega.boundaryParam t *
            (Omega.boundaryParam t - xi)⁻¹ -
          star (deriv Omega.boundaryParam t *
            (Omega.boundaryParam t - xi)⁻¹)) := by
  let a := deriv Omega.boundaryParam t *
    (Omega.boundaryParam t - xi)⁻¹
  change (((a.im / Real.pi : ℝ) : ℂ)) =
    (2 * (Real.pi : ℂ) * I)⁻¹ * (a - star a)
  rw [Complex.star_def, RCLike.sub_conj]
  change (((a.im / Real.pi : ℝ) : ℂ)) =
    (2 * (Real.pi : ℂ) * I)⁻¹ * (2 * (a.im : ℂ) * I)
  rw [ofReal_div]
  field_simp [Real.pi_ne_zero, I_ne_zero]
