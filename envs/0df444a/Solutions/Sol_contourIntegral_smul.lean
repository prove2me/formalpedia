-- Prove2me | solution 1 for contourIntegral_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:36:41.214143+00:00
-- url     : https://prove2.me/submissions/72dff2cd-4b74-48ce-869b-ab8dbd906bb9

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral

set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
theorem _root_.solution (a : ℂ) (f : ℂ → F) (γ : ℝ → ℂ) :
    contourIntegral (fun z => a • f z) γ = a • contourIntegral f γ := by
  unfold contourIntegral
  have h : (fun t => deriv γ t • a • f (γ t)) = fun t => a • deriv γ t • f (γ t) :=
    funext fun t => smul_comm _ _ _
  rw [h]
  exact intervalIntegral.integral_smul a _
