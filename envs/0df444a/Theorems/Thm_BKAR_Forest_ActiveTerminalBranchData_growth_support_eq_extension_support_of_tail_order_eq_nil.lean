-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_support_eq_extension_support_of_tail_order_eq_nil
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_support_eq_extension_support_of_tail_order_eq_nil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:24:44.39742+00:00
-- url     : https://prove2.me/theorems/5395123a-9bbc-4f7a-a0a1-70a3897c77bf
-- title:
--   Active Terminal Branch Data: growth support eq extension support of tail order eq nil
-- statement:
--   If the selected tail after an active edge has empty order, then the full
--   branch support is just the support of the one-edge extension.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L399-L405
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L399-L405

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

theorem BKAR.Forest.ActiveTerminalBranchData.growth_support_eq_extension_support_of_tail_order_eq_nil
    (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (htail : (data.tail e).order = []) :
    (data.growth e).support = (data.extension e).forest.support := by sorry
