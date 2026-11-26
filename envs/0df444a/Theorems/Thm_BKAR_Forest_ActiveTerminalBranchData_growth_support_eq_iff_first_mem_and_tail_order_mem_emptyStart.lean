-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_support_eq_iff_first_mem_and_tail_order_mem_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_support_eq_iff_first_mem_and_tail_order_mem_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:55:19.411648+00:00
-- url     : https://prove2.me/theorems/b330bc08-706f-43ae-ac23-15fdc3b9a478
-- title:
--   Active Terminal Branch Data: growth support eq iff first mem and tail order mem empty Start
-- statement:
--   Support equality for a selected terminal branch from the empty forest is
--   equivalent to choosing the first edge in the support and a canonical ordering
--   of the support with that edge erased.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L158-L183
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L158-L183

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

theorem BKAR.Forest.ActiveTerminalBranchData.growth_support_eq_iff_first_mem_and_tail_order_mem_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (I : ForestIndex V) :
    (data.growth e).support = I ↔
      e.val ∈ I.edges ∧
        (data.tail e).order ∈ edgeSetOrders (I.edges.erase e.val) := by sorry
