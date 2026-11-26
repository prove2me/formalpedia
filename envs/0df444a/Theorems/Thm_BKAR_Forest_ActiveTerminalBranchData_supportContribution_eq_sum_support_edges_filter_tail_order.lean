-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_eq_sum_support_edges_filter_tail_order
-- name    : BKAR.Forest.ActiveTerminalBranchData.supportContribution_eq_sum_support_edges_filter_tail_order
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:55:39.969553+00:00
-- url     : https://prove2.me/theorems/faa2d7c2-5765-5de2-8fbd-2063e04caa5d
-- title:
--   Active Terminal Branch Data: support Contribution eq sum support edges filter tail order
-- statement:
--   Support-fiber form indexed directly by first edges in `I.edges`.  Since every
--   edge is active over the empty forest, the ambient active-edge filter can be
--   collapsed to the actual support edge set, with the tail order carrying the
--   remaining fiber predicate.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L219-L259
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L219-L259

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.supportContribution_eq_sum_support_edges_filter_tail_order
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ =
      Finset.sum
        (I.edges.attach.filter
          (fun e =>
            (data.tail (emptyActiveEdge e.val)).order ∈
              edgeSetOrders (I.edges.erase e.val)))
        (fun e => (data.growth (emptyActiveEdge e.val)).terminal.orderedContribution
          (data.growthOrder (emptyActiveEdge e.val)) ρ) := by sorry
