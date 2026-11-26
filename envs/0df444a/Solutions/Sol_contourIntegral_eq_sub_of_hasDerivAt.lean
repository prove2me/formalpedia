-- Prove2me | solution 1 for contourIntegral_eq_sub_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:44:04.771465+00:00
-- url     : https://prove2.me/submissions/035e8c21-3d26-488e-8b86-c89d4b0deb2f

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral

set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
theorem _root_.solution [CompleteSpace F] {f Fp : ℂ → F} {γ : ℝ → ℂ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) (2 * π), DifferentiableAt ℝ γ t)
    (hF : ∀ t ∈ Icc (0 : ℝ) (2 * π), HasDerivAt Fp (f (γ t)) (γ t))
    (hint : ContourIntegrable f γ) :
    contourIntegral f γ = Fp (γ (2 * π)) - Fp (γ 0) := by
  unfold ContourIntegrable at hint
  unfold contourIntegral
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => Fp (γ t)) (fun t ht => ?_) hint
  rw [uIcc_of_le Real.two_pi_pos.le] at ht
  exact (hF t ht).scomp t (hγ t ht).hasDerivAt
