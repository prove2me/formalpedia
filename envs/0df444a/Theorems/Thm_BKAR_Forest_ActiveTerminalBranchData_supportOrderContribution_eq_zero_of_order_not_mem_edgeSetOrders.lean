-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportOrderContribution_eq_zero_of_order_not_mem_edgeSetOrders
-- name    : BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_eq_zero_of_order_not_mem_edgeSetOrders
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:29:26.48626+00:00
-- url     : https://prove2.me/theorems/91b28e47-79bc-519c-8322-fc5ed944f30b
-- title:
--   Active Terminal Branch Data: support Order Contribution eq zero of order not mem edge Set Orders
-- statement:
--   An order outside `edgeSetOrders I.edges` has no selected branch in the support
--   `I` fiber.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L29-L41
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L29-L41

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_eq_zero_of_order_not_mem_edgeSetOrders
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) {order : List (Edge V)}
    (horder : order ∉ edgeSetOrders I.edges)
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I order ρ = 0 := by sorry
