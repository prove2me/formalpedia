-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_local_chain_midpoint_admissible
-- name    : BirkhoffGlobalSection.local_chain_midpoint_admissible
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:27.715975+00:00
-- url     : https://prove2.me/theorems/90298749-8420-4c02-a919-7e6a9e1ca66c
-- title:
--   local chain midpoint admissible
-- statement:
--   If two short successive edges lie near a point where the set is locally convex, replacing their shared vertex by the endpoint midpoint preserves the displayed convex-set membership and edge distance bounds. The exact regularity, compactness, nonzero and uniqueness hypotheses displayed in the formal statement are retained.
-- source:
--   Independent extraction from accepted source Solutions/Sol_BirkhoffGlobalSection_closed_preconnected_locally_convex_is_convex.lean:182. Local normalization abbreviations and map definitions are expanded explicitly in the statement. Exact mathematical scope retained; no global-section conclusion.

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

theorem BirkhoffGlobalSection.local_chain_midpoint_admissible (K B : Set Phase) (hB : Convex ℝ B)
    (a b c : Phase) (ha : a ∈ K ∩ B) (hc : c ∈ K ∩ B)
    (δ ε : ℝ) (hεδ : ε < δ)
    (hlab : dist a b ≤ ε) (hrbc : dist b c ≤ ε)
    (hloc : Convex ℝ (K ∩ ball b δ)) :
    (1 / 2 : ℝ) • (a + c) ∈ K ∩ B ∧
      dist a ((1 / 2 : ℝ) • (a + c)) ≤ ε ∧
      dist ((1 / 2 : ℝ) • (a + c)) c ≤ ε := by sorry
