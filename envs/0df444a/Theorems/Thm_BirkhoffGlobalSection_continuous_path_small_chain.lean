-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_continuous_path_small_chain
-- name    : BirkhoffGlobalSection.continuous_path_small_chain
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:30.359817+00:00
-- url     : https://prove2.me/theorems/435103ee-53ac-4197-89cf-bb267a4d5610
-- title:
--   continuous path small chain
-- statement:
--   A continuous unit-interval path contained in a phase-space set can be sampled as a finite chain with the same endpoints, all vertices in the set, and successive distances below any prescribed positive tolerance. The exact regularity, compactness, nonzero and uniqueness hypotheses displayed in the formal statement are retained.
-- source:
--   Independent extraction from accepted source Solutions/Sol_BirkhoffGlobalSection_closed_preconnected_locally_convex_is_convex.lean:112. Local normalization abbreviations and map definitions are expanded explicitly in the statement. Exact mathematical scope retained; no global-section conclusion.

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

theorem BirkhoffGlobalSection.continuous_path_small_chain (C : Set Phase) (γ : I → Phase)
    (hγ : Continuous γ) (hC : ∀ t, γ t ∈ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ p : Fin (N + 1) → Phase,
      p 0 = γ 0 ∧ p (Fin.last N) = γ 1 ∧
      (∀ i, p i ∈ C) ∧ (∀ i : Fin N, dist (p i.castSucc) (p i.succ) < ε) := by sorry
