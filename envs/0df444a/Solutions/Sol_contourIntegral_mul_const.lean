-- Prove2me | solution 1 for contourIntegral_mul_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:40:33.793938+00:00
-- url     : https://prove2.me/submissions/eec83890-5993-4fd9-8071-99fc8cc06ce6

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
    contourIntegral (fun z => f z * b) γ = contourIntegral f γ * b := by
  let L : B →L[ℂ] B := (ContinuousLinearMap.mul ℂ B).flip b
  simpa only [L, ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using
    L.contourIntegral_comp_comm hf
