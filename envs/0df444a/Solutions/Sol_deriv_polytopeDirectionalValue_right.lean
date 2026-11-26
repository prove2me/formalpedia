-- Prove2me | solution 1 for deriv_polytopeDirectionalValue_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:09.628049+00:00
-- url     : https://prove2.me/submissions/68548998-8dc5-4a61-9401-7d82fe3c3e0c

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange

set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
theorem _root_.solution (z : ℂ) (theta : ℝ) :
    deriv (polytopeDirectionalValue z) theta =
      -z.re * Real.sin theta + z.im * Real.cos theta := by
  unfold polytopeDirectionalValue
  change deriv
    ((fun _ : ℝ => z.re) * Real.cos + (fun _ : ℝ => z.im) * Real.sin)
      theta = _
  rw [deriv_add
    ((differentiableAt_const z.re).mul Real.differentiableAt_cos)
    ((differentiableAt_const z.im).mul Real.differentiableAt_sin),
    deriv_mul (differentiableAt_const z.re) Real.differentiableAt_cos,
    deriv_mul (differentiableAt_const z.im) Real.differentiableAt_sin,
    deriv_const, deriv_const, Real.deriv_cos, Real.deriv_sin]
  ring
