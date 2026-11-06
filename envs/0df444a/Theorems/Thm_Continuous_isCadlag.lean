-- Prove2me | Theorems.Thm_Continuous_isCadlag
-- name    : Continuous.isCadlag
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:35:37.535783+00:00
-- url     : https://prove2.me/theorems/5b765299-da13-4d70-abe4-464dc5d56917
-- title:
--   LeanLevy: Continuous.isCadlag
-- statement:
--   A continuous function is càdlàg: it is continuous within `[t, ∞)` and its left limit is Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/Cadlag.lean#L281

import Definitions.Def_LeanLevy_Processes_Cadlag
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Algebra.Monoid

universe u_1 u_2
theorem Continuous.isCadlag : ∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : Preorder α]
  {f : α → β}, @Continuous α β inst inst_1 f → @ProbabilityTheory.IsCadlag α β inst inst_1 inst_2 f := by sorry
