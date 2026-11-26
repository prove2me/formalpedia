-- Prove2me | solution 1 for contourIntegral_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:36:41.819146+00:00
-- url     : https://prove2.me/submissions/ec974c9e-5974-4cff-860c-c14233d3fa1e

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Theorems.Thm_ContinuousLinearMap_contourIntegral_comp_comm

set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
theorem _root_.solution {f : ℂ → B} {γ : ℝ → ℂ} (b : B)
    (hf : ContourIntegrable f γ) :
    contourIntegral (fun z => b * f z) γ = b * contourIntegral f γ := by
  let L : B →L[ℂ] B := ContinuousLinearMap.mul ℂ B b
  simpa only [L, ContinuousLinearMap.mul_apply'] using L.contourIntegral_comp_comm hf
