-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_two_term_sum_comparison
-- name    : BirkhoffGlobalSection.two_term_sum_comparison
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T22:39:26.263565+00:00
-- url     : https://prove2.me/theorems/b0164f30-9f33-42dd-8fd1-914b4b372ec4
-- title:
--   two term sum comparison
-- statement:
--   For two real-valued functions on a finite type that agree outside two distinct indices, an inequality between their total sums implies the corresponding inequality between the two exceptional terms. The exact regularity, compactness, nonzero and uniqueness hypotheses displayed in the formal statement are retained.
-- source:
--   Independent extraction from accepted source Solutions/Sol_BirkhoffGlobalSection_closed_preconnected_locally_convex_is_convex.lean:206. Local normalization abbreviations and map definitions are expanded explicitly in the statement. Exact mathematical scope retained; no global-section conclusion.

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

theorem BirkhoffGlobalSection.two_term_sum_comparison {ι : Type*} [Fintype ι]
    (f g : ι → ℝ) (u v : ι) (huv : u ≠ v)
    (hsame : ∀ i, i ≠ u → i ≠ v → f i = g i)
    (hle : (∑ i, f i) ≤ ∑ i, g i) : f u + f v ≤ g u + g v := by sorry
