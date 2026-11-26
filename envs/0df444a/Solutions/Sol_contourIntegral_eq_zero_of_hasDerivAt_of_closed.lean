-- Prove2me | solution 1 for contourIntegral_eq_zero_of_hasDerivAt_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:44:44.900257+00:00
-- url     : https://prove2.me/submissions/6fac76d5-7f29-4dc8-8b7a-f567f76ba0a7

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Theorems.Thm_contourIntegral_eq_sub_of_hasDerivAt

set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
theorem _root_.solution {f Fp : ℂ → F} {γ : ℝ → ℂ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) (2 * π), DifferentiableAt ℝ γ t)
    (hF : ∀ t ∈ Icc (0 : ℝ) (2 * π), HasDerivAt Fp (f (γ t)) (γ t))
    (hint : ContourIntegrable f γ) (hclosed : γ (2 * π) = γ 0) :
    contourIntegral f γ = 0 := by
  classical
  by_cases hcomplete : CompleteSpace F
  · let _ : CompleteSpace F := hcomplete
    rw [contourIntegral_eq_sub_of_hasDerivAt hγ hF hint, hclosed, sub_self]
  · unfold contourIntegral intervalIntegral
    rw [integral_of_not_completeSpace hcomplete, integral_of_not_completeSpace hcomplete,
      sub_self]
