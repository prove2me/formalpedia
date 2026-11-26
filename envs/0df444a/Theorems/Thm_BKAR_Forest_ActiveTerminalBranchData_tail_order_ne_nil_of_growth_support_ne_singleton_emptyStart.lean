-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_tail_order_ne_nil_of_growth_support_ne_singleton_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.tail_order_ne_nil_of_growth_support_ne_singleton_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:01:57.537928+00:00
-- url     : https://prove2.me/theorems/a945be07-e926-5da0-947d-df8bbf20bfa5
-- title:
--   Active Terminal Branch Data: tail order ne nil of growth support ne singleton empty Start
-- statement:
--   If the selected terminal support is not the singleton of its first edge, then
--   the branch has a nonempty tail order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L235-L244
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L235-L244

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.tail_order_ne_nil_of_growth_support_ne_singleton_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (hsupport :
      (data.growth e).support ≠ ForestIndex.singleton e.val) :
    (data.tail e).order ≠ [] := by sorry
