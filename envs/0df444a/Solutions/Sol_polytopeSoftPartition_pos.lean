-- Prove2me | solution 1 for polytopeSoftPartition_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:57:54.034129+00:00
-- url     : https://prove2.me/submissions/0e2940c2-e943-491b-94d1-62255c67f88f

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution {u : Finset ℂ} (hu : u.Nonempty)
    (delta theta : ℝ) :
    0 < polytopeSoftPartition u delta theta := by
  unfold polytopeSoftPartition
  exact Finset.sum_pos (fun z hz => Real.exp_pos _) hu
