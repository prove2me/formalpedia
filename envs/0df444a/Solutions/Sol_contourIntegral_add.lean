-- Prove2me | solution 1 for contourIntegral_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:38:25.027713+00:00
-- url     : https://prove2.me/submissions/85b64bc0-1eef-4ee6-845f-7d1c06910a7c

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral

set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
theorem _root_.solution {f g : ℂ → F} {γ : ℝ → ℂ} (hf : ContourIntegrable f γ)
    (hg : ContourIntegrable g γ) :
    contourIntegral (fun z => f z + g z) γ = contourIntegral f γ + contourIntegral g γ := by
  unfold contourIntegral
  simp only [smul_add]
  exact intervalIntegral.integral_add hf hg
