-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radialDirectionMap_bijective
-- name    : BirkhoffGlobalSection.radialDirectionMap_bijective
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:35.471212+00:00
-- url     : https://prove2.me/theorems/9b0df279-19d7-44c6-beb2-8b8c5a707165
-- title:
--   radialDirectionMap bijective
-- statement:
--   For a phase-space subset avoiding zero, normalized direction is a bijection onto the norm-one sphere if the subset meets every positive unit ray exactly once. The exact regularity, compactness, nonzero and uniqueness hypotheses displayed in the formal statement are retained.
-- source:
--   Independent extraction from accepted source Solutions/Sol_BirkhoffGlobalSection_radial_filling_locally_convex_at_each_point.lean:325. Local normalization abbreviations and map definitions are expanded explicitly in the statement. Exact mathematical scope retained; no global-section conclusion.

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

theorem BirkhoffGlobalSection.radialDirectionMap_bijective (S : Set Phase) (hsne : ∀ s ∈ S, s ≠ 0)
    (hray : ∀ x : Phase, ‖x‖ = 1 → ∃ r : ℝ, 0 < r ∧ r • x ∈ S)
    (huniq : ∀ x : Phase, ‖x‖ = 1 → ∀ r t : ℝ, 0 < r → 0 < t →
      r • x ∈ S → t • x ∈ S → r = t) :
    Function.Bijective ((fun s : S => (⟨normalize (s : Phase), norm_normalize (hsne s s.property)⟩ : ({x : Phase // ‖x‖ = 1})))) := by sorry
