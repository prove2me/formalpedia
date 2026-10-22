-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_locallyConvexSet_uniform_radius
-- name    : BirkhoffGlobalSection.locallyConvexSet_uniform_radius
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:24.807739+00:00
-- url     : https://prove2.me/theorems/8539ee04-872d-452d-aa29-05dce0675f4d
-- title:
--   locallyConvexSet uniform radius
-- statement:
--   For a compact subset A of a locally convex phase-space set K, one positive ball radius makes K intersected with the ball about every point of A convex. The exact regularity, compactness, nonzero and uniqueness hypotheses displayed in the formal statement are retained.
-- source:
--   Independent extraction from accepted source Solutions/Sol_BirkhoffGlobalSection_closed_preconnected_locally_convex_is_convex.lean:40. Local normalization abbreviations and map definitions are expanded explicitly in the statement. Exact mathematical scope retained; no global-section conclusion.

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

theorem BirkhoffGlobalSection.locallyConvexSet_uniform_radius (K A : Set Phase) (hA : IsCompact A)
    (hAK : A ⊆ K)
    (hloc : ∀ x ∈ K, ∃ U : Set Phase, U ∈ 𝓝 x ∧ Convex ℝ (K ∩ U)) :
    ∃ δ > 0, ∀ x ∈ A, Convex ℝ (K ∩ ball x δ) := by sorry
