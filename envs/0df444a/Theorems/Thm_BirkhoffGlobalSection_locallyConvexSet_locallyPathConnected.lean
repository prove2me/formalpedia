-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_locallyConvexSet_locallyPathConnected
-- name    : BirkhoffGlobalSection.locallyConvexSet_locallyPathConnected
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:23.530975+00:00
-- url     : https://prove2.me/theorems/55a06673-077d-4495-a37c-5108123192f9
-- title:
--   locallyConvexSet locallyPathConnected
-- statement:
--   A locally convex phase-space subset is locally path connected in its subtype topology. The exact regularity, compactness, nonzero and uniqueness hypotheses displayed in the formal statement are retained.
-- source:
--   Independent extraction from accepted source Solutions/Sol_BirkhoffGlobalSection_closed_preconnected_locally_convex_is_convex.lean:18. Local normalization abbreviations and map definitions are expanded explicitly in the statement. Exact mathematical scope retained; no global-section conclusion.

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.ProperSpace

open scoped Topology
open Set Metric Filter
open BirkhoffGlobalSection


open BirkhoffGlobalSection NormedSpace Set Metric Filter
open scoped Topology unitInterval BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem BirkhoffGlobalSection.locallyConvexSet_locallyPathConnected (K : Set Phase)
    (hloc : ∀ x ∈ K, ∃ U : Set Phase, U ∈ 𝓝 x ∧ Convex ℝ (K ∩ U)) :
    LocallyPathConnectedSpace K := by sorry
