-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radialDirectionMap_continuous
-- name    : BirkhoffGlobalSection.radialDirectionMap_continuous
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:34.262752+00:00
-- url     : https://prove2.me/theorems/5ebe80e4-4f5d-480c-a0ba-c44c1289ac63
-- title:
--   radialDirectionMap continuous
-- statement:
--   Normalizing the nonzero points of a phase-space subset to the norm-one sphere defines a continuous map on the subset. The exact regularity, compactness, nonzero and uniqueness hypotheses displayed in the formal statement are retained.
-- source:
--   Independent extraction from accepted source Solutions/Sol_BirkhoffGlobalSection_radial_filling_locally_convex_at_each_point.lean:318. Local normalization abbreviations and map definitions are expanded explicitly in the statement. Exact mathematical scope retained; no global-section conclusion.

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

theorem BirkhoffGlobalSection.radialDirectionMap_continuous (S : Set Phase) (hsne : ∀ s ∈ S, s ≠ 0) :
    Continuous ((fun s : S => (⟨normalize (s : Phase), norm_normalize (hsne s s.property)⟩ : ({x : Phase // ‖x‖ = 1})))) := by sorry
