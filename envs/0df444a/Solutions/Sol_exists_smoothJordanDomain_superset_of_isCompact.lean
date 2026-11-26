-- Prove2me | solution 1 for exists_smoothJordanDomain_superset_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:44:08.485535+00:00
-- url     : https://prove2.me/submissions/c1fc3f7e-37a6-4c6e-8d22-be62deea273f

import Mathlib.Analysis.Convex.Strict
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox

set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
theorem _root_.solution (K : Set ℂ) (hK : IsCompact K) :
    ∃ Ω : SmoothJordanDomain, K ⊆ Ω.carrier := by
  obtain ⟨R, hR, hsub⟩ := hK.isBounded.subset_ball_lt 0 0
  exact ⟨SmoothJordanDomain.ball 0 R hR, hsub⟩
