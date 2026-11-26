-- Prove2me | solution 1 for normalized_circleIntegral_zpow_smul_resolvent_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:21:40.908808+00:00
-- url     : https://prove2.me/submissions/ec5dc1ef-404a-41b5-af28-293c7f313b2c

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Theorems.Thm_normalized_circleIntegral_zpow_smul_resolvent_eq_pow_of_normOne

set_option autoImplicit false
open Complex Set spectrum TopologicalSpace
open scoped Real Interval
universe u
variable {B : Type u} [NormedRing B] [NormedAlgebra ℂ B]
variable [CompleteSpace B]
variable [NormOneClass B]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (n : ℕ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => z ^ n • resolvent A z) 0 R = A ^ n := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    exact Subsingleton.elim _ _
  · let _ := hE
    exact normalized_circleIntegral_zpow_smul_resolvent_eq_pow_of_normOne A hR n
