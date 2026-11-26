-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportOrderContribution_cons_eq_orderedContribution_of_support_eq_and_tail_eq
-- name    : BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_cons_eq_orderedContribution_of_support_eq_and_tail_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:01:45.370562+00:00
-- url     : https://prove2.me/theorems/2a2cf42a-5b71-4398-a72d-6e8a8dd3211e
-- title:
--   Active Terminal Branch Data: support Order Contribution cons eq ordered Contribution of support eq and tail eq
-- statement:
--   A fixed nonempty ordered sector can only be supplied by the branch whose first
--   edge is the head of that order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L60-L91
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L60-L91

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

theorem BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_cons_eq_orderedContribution_of_support_eq_and_tail_eq
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (a : Edge V) (tail : List (Edge V))
    (hsupport : (data.growth (emptyActiveEdge a)).support = I)
    (htail : (data.tail (emptyActiveEdge a)).order = tail)
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I (a :: tail) ρ =
      (data.growth (emptyActiveEdge a)).terminal.orderedContribution
        (a :: tail) ρ := by sorry
