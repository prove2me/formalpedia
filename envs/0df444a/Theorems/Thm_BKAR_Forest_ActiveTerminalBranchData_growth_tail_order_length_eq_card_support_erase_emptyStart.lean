-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_tail_order_length_eq_card_support_erase_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_tail_order_length_eq_card_support_erase_emptyStart
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:29:15.588997+00:00
-- url     : https://prove2.me/theorems/e2ed7089-8e9b-5483-9b6f-c78efd33992a
-- title:
--   Active Terminal Branch Data: growth tail order length eq card support erase empty Start
-- statement:
--   Over a fixed support fiber, the tail branch has exactly the number of edges
--   left after erasing the selected first edge.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L339-L346
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L339-L346

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

theorem BKAR.Forest.ActiveTerminalBranchData.growth_tail_order_length_eq_card_support_erase_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    {I : ForestIndex V} (hsupport : (data.growth e).support = I) :
    (data.tail e).order.length = (I.edges.erase e.val).card := by sorry
