-- Prove2me | solution 1 for contourIntegral_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:40:24.483959+00:00
-- url     : https://prove2.me/submissions/dbd09d3b-7b56-4da2-bdda-13ea34455479

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral

set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
theorem _root_.solution {f g : ℂ → F} {γ : ℝ → ℂ} (hf : ContourIntegrable f γ)
    (hg : ContourIntegrable g γ) :
    contourIntegral (fun z => f z - g z) γ = contourIntegral f γ - contourIntegral g γ := by
  unfold contourIntegral
  simp only [smul_sub]
  exact intervalIntegral.integral_sub hf hg
