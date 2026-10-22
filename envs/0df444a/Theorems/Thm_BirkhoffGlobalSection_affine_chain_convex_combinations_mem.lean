-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_affine_chain_convex_combinations_mem
-- name    : BirkhoffGlobalSection.affine_chain_convex_combinations_mem
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:34.215752+00:00
-- url     : https://prove2.me/theorems/56ae15db-bb07-4b0f-a036-30b95b42f52e
-- title:
--   affine chain convex combinations mem
-- statement:
--   For an affine chain in a locally convex set with sufficiently short edges and the displayed uniform convex-neighborhood bounds, every convex combination of its two endpoints belongs to the set. The exact regularity, compactness, nonzero and uniqueness hypotheses displayed in the formal statement are retained.
-- source:
--   Independent extraction from accepted source Solutions/Sol_BirkhoffGlobalSection_closed_preconnected_locally_convex_is_convex.lean:368. Local normalization abbreviations and map definitions are expanded explicitly in the statement. Exact mathematical scope retained; no global-section conclusion.

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

theorem BirkhoffGlobalSection.affine_chain_convex_combinations_mem (K : Set Phase) (N : ℕ) (hN : 0 < N)
    (p : Fin (N + 1) → Phase) (d : Phase)
    (haff : ∀ k, p k = p 0 + (k.val : ℝ) • d)
    (hpmem : ∀ k, p k ∈ K) (δ ε : ℝ) (hδ : 0 < δ) (hεδ : ε < δ)
    (hedge : ∀ i : Fin N, dist (p i.castSucc) (p i.succ) ≤ ε)
    (hloc : ∀ k, Convex ℝ (K ∩ ball (p k) δ))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • p 0 + b • p (Fin.last N) ∈ K := by sorry
