-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radial_ray_representation
-- name    : BirkhoffGlobalSection.radial_ray_representation
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:17.200993+00:00
-- url     : https://prove2.me/theorems/854b2542-d06b-4e49-9398-72645e9ec45f
-- title:
--   Radial ray representation
-- statement:
--   Every nonzero four-dimensional phase vector is a positive scalar multiple of a point on the unit three-sphere.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Original auxiliary result from the accepted source Solutions/Sol_BirkhoffGlobalSection_radial_filling_locally_convex_at_each_point.lean:28. Exact quantified statement retained; foundational calculus and geometry are imported from Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue


open BirkhoffGlobalSection


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.radial_ray_representation (s : Phase) (hs : s ≠ 0) :
    ∃ x ∈ unitThreeSphere, ∃ R : ℝ, 0 < R ∧ (fun i : Fin 4 => R * x i) = s := by sorry
