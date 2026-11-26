-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_extension_activeEdges_eq_empty_of_tail_order_eq_nil
-- name    : BKAR.Forest.ActiveTerminalBranchData.extension_activeEdges_eq_empty_of_tail_order_eq_nil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:52:59.3656+00:00
-- url     : https://prove2.me/theorems/147ce9dd-60fb-5ce5-8b56-ae80160ec85d
-- title:
--   Active Terminal Branch Data: extension active Edges eq empty of tail order eq nil
-- statement:
--   If the selected tail after an active edge has empty order, terminality of the
--   tail says that the one-edge extension is already terminal.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L411-L417
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L411-L417

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.extension_activeEdges_eq_empty_of_tail_order_eq_nil
    (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (htail : (data.tail e).order = []) :
    (data.extension e).forest.activeEdges = ∅ := by sorry
