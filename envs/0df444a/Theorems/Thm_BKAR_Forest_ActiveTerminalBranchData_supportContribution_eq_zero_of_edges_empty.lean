-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_eq_zero_of_edges_empty
-- name    : BKAR.Forest.ActiveTerminalBranchData.supportContribution_eq_zero_of_edges_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:29:50.345532+00:00
-- url     : https://prove2.me/theorems/82f911fb-ee44-5781-9fe5-36876d910485
-- title:
--   Active Terminal Branch Data: support Contribution eq zero of edges empty
-- statement:
--   No selected active-terminal branch from the empty forest has empty terminal
--   support.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L170-L184
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L170-L184

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.supportContribution_eq_zero_of_edges_empty
    (data : ActiveTerminalBranchData (Forest.empty V))
    {I : ForestIndex V} (hI : I.edges = ∅)
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ = 0 := by sorry
