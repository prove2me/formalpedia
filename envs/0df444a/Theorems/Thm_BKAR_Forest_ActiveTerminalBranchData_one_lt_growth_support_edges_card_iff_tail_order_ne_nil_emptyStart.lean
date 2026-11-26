-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_one_lt_growth_support_edges_card_iff_tail_order_ne_nil_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.one_lt_growth_support_edges_card_iff_tail_order_ne_nil_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:29:54.729855+00:00
-- url     : https://prove2.me/theorems/220bcc90-0b57-4d67-b658-3e39c3db03c3
-- title:
--   Active Terminal Branch Data: one lt growth support edges card iff tail order ne nil empty Start
-- statement:
--   For selected empty-start terminal branches, higher-support fibers are exactly
--   the branches whose selected tail order is nonempty.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L290-L302
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L290-L302

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

theorem BKAR.Forest.ActiveTerminalBranchData.one_lt_growth_support_edges_card_iff_tail_order_ne_nil_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    1 < (data.growth e).support.edges.card ↔
      (data.tail e).order ≠ [] := by sorry
