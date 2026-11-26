-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_tail_order_ne_nil_of_one_lt_support_edges_card_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.tail_order_ne_nil_of_one_lt_support_edges_card_emptyStart
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:02:19.276031+00:00
-- url     : https://prove2.me/theorems/a52f9200-c955-4a83-9f6d-18dcd5f5644f
-- title:
--   Active Terminal Branch Data: tail order ne nil of one lt support edges card empty Start
-- statement:
--   Branches over a support with more than one edge have a genuinely nonempty
--   tail after the first selected edge.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L250-L263
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L250-L263

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

theorem BKAR.Forest.ActiveTerminalBranchData.tail_order_ne_nil_of_one_lt_support_edges_card_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    {I : ForestIndex V} (hsupport : (data.growth e).support = I)
    (hcard : 1 < I.edges.card) :
    (data.tail e).order ≠ [] := by sorry
