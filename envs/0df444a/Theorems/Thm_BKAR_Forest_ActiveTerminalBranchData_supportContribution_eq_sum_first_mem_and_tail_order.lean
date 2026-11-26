-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_eq_sum_first_mem_and_tail_order
-- name    : BKAR.Forest.ActiveTerminalBranchData.supportContribution_eq_sum_first_mem_and_tail_order
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:55:23.741706+00:00
-- url     : https://prove2.me/theorems/b747e02a-9d79-5fb3-b579-aece4fd161ee
-- title:
--   Active Terminal Branch Data: support Contribution eq sum first mem and tail order
-- statement:
--   First-edge/tail-order form of `ActiveTerminalBranchData.supportContribution`.
--   This is the support-fiber shape used by the recursive BKAR sector enumeration.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L189-L211
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L189-L211

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

theorem BKAR.Forest.ActiveTerminalBranchData.supportContribution_eq_sum_first_mem_and_tail_order
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e => e.val ∈ I.edges ∧
            (data.tail e).order ∈ edgeSetOrders (I.edges.erase e.val)))
        (fun e => (data.growth e).terminal.orderedContribution
          (data.growthOrder e) ρ) := by sorry
