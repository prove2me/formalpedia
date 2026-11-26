-- Prove2me | solution 1 for normalized_circleIntegral_resolvent_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:54:11.577933+00:00
-- url     : https://prove2.me/submissions/37c4d7d3-c761-4430-9567-8bff3895bd33

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Theorems.Thm_normalized_circleIntegral_resolvent_eq_one_of_normOne

set_option autoImplicit false
open Complex Set spectrum TopologicalSpace
open scoped Real Interval
universe u
variable {B : Type u} [NormedRing B] [NormedAlgebra ℂ B]
variable [CompleteSpace B]
variable [NormOneClass B]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) :
    (2 * (Real.pi : ℂ) * I)⁻¹ • circleIntegral (resolvent A) 0 R =
      (1 : E →L[ℂ] E) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    exact Subsingleton.elim _ _
  · let _ := hE
    exact normalized_circleIntegral_resolvent_eq_one_of_normOne A hR
