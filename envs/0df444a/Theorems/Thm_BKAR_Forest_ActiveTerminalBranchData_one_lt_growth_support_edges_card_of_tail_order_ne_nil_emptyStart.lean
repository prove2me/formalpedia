-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_one_lt_growth_support_edges_card_of_tail_order_ne_nil_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.one_lt_growth_support_edges_card_of_tail_order_ne_nil_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:02:10.052416+00:00
-- url     : https://prove2.me/theorems/3b0e9f92-fc0e-48f9-a32b-13cdd0345e1f
-- title:
--   Active Terminal Branch Data: one lt growth support edges card of tail order ne nil empty Start
-- statement:
--   Conversely, if the selected empty-start branch has a nonempty tail, its
--   terminal support has at least two edges.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L269-L284
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L269-L284

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

theorem BKAR.Forest.ActiveTerminalBranchData.one_lt_growth_support_edges_card_of_tail_order_ne_nil_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (htail : (data.tail e).order ≠ []) :
    1 < (data.growth e).support.edges.card := by sorry
