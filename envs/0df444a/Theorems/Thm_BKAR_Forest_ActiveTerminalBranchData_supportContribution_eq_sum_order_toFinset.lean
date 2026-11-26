-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_eq_sum_order_toFinset
-- name    : BKAR.Forest.ActiveTerminalBranchData.supportContribution_eq_sum_order_toFinset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:55:29.3085+00:00
-- url     : https://prove2.me/theorems/87d0154c-e1fb-46b4-a31b-f8b77ee4dca7
-- title:
--   Active Terminal Branch Data: support Contribution eq sum order to Finset
-- statement:
--   Edge-set form of `ActiveTerminalBranchData.supportContribution`. This removes
--   the proof-carrying support index from the fiber predicate.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L133-L151
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L133-L151

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

theorem BKAR.Forest.ActiveTerminalBranchData.supportContribution_eq_sum_order_toFinset
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e => (e.val :: (data.tail e).order).toFinset = I.edges))
        (fun e => (data.growth e).terminal.orderedContribution
          (data.growthOrder e) ρ) := by sorry
