-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_order_length_eq_card_support_edges_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_order_length_eq_card_support_edges_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:56:05.714856+00:00
-- url     : https://prove2.me/theorems/a2f1e239-5395-45d5-b22f-58d5bfa91c20
-- title:
--   Active Terminal Branch Data: growth order length eq card support edges empty Start
-- statement:
--   The selected first-edge/tail order has length equal to the cardinality of its
--   support edge set.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L367-L374
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L367-L374

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

theorem BKAR.Forest.ActiveTerminalBranchData.growth_order_length_eq_card_support_edges_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    {I : ForestIndex V} (hsupport : (data.growth e).support = I) :
    (e.val :: (data.tail e).order).length = I.edges.card := by sorry
