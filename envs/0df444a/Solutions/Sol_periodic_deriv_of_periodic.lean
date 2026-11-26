-- Prove2me | solution 1 for periodic_deriv_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:22:42.151852+00:00
-- url     : https://prove2.me/submissions/714d8fa9-4dd0-41a4-afa5-6fa4304f2f8d

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution {f : ℝ → ℝ} {p : ℝ}
    (hf : Function.Periodic f p) :
    Function.Periodic (deriv f) p := by
  intro x
  calc
    deriv f (x + p) = deriv (fun y => f (y + p)) x := by
      rw [deriv_comp_add_const]
    _ = deriv f x := by rw [hf.funext]
