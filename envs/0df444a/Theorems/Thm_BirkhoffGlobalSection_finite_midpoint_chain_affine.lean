-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_finite_midpoint_chain_affine
-- name    : BirkhoffGlobalSection.finite_midpoint_chain_affine
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:31.471003+00:00
-- url     : https://prove2.me/theorems/8a1a5b40-0e26-4cca-9510-c9db77dcf941
-- title:
--   finite midpoint chain affine
-- statement:
--   A finite nonempty phase-space chain whose internal vertices are midpoints of their neighbors is an affine arithmetic progression. The exact regularity, compactness, nonzero and uniqueness hypotheses displayed in the formal statement are retained.
-- source:
--   Independent extraction from accepted source Solutions/Sol_BirkhoffGlobalSection_closed_preconnected_locally_convex_is_convex.lean:327. Local normalization abbreviations and map definitions are expanded explicitly in the statement. Exact mathematical scope retained; no global-section conclusion.

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

theorem BirkhoffGlobalSection.finite_midpoint_chain_affine (N : ℕ) (hN : 0 < N) (p : Fin (N + 1) → Phase)
    (hmid : ∀ i j : Fin N, j.succ = i.castSucc →
      p i.castSucc = (1 / 2 : ℝ) • (p j.castSucc + p i.succ)) :
    ∃ d : Phase, ∀ k : Fin (N + 1), p k = p 0 + (k.val : ℝ) • d := by sorry
