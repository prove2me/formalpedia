-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radial_coordinates_strict_inside_is_interior
-- name    : BirkhoffGlobalSection.radial_coordinates_strict_inside_is_interior
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:38.380737+00:00
-- url     : https://prove2.me/theorems/36ebd49f-9312-487c-bd21-d00901b5874c
-- title:
--   radial coordinates strict inside is interior
-- statement:
--   For supplied continuous radial coordinates characterizing filling membership by factor at most one, every nonzero vector with factor strictly below one lies in the filling interior. The exact regularity, compactness, nonzero and uniqueness hypotheses displayed in the formal statement are retained.
-- source:
--   Independent extraction from accepted source Solutions/Sol_BirkhoffGlobalSection_radial_filling_locally_convex_at_each_point.lean:468. Local normalization abbreviations and map definitions are expanded explicitly in the statement. Exact mathematical scope retained; no global-section conclusion.

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


open BirkhoffGlobalSection NormedSpace Set Metric Filter
open scoped Topology unitInterval BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem BirkhoffGlobalSection.radial_coordinates_strict_inside_is_interior (S : Set Phase)
    (τ : ({x : Phase // x ≠ 0}) → ℝ) (hτ : Continuous τ)
    (hK : ∀ y : ({x : Phase // x ≠ 0}), (y : Phase) ∈
      {z | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = t • s} ↔ τ y ≤ 1)
    (x : ({x : Phase // x ≠ 0})) (hx : τ x < 1) :
    (x : Phase) ∈ interior {z | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = t • s} := by sorry
