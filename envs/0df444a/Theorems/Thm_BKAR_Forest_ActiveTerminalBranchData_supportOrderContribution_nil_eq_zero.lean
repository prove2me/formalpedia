-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportOrderContribution_nil_eq_zero
-- name    : BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_nil_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:29:30.145183+00:00
-- url     : https://prove2.me/theorems/7cd400e0-ca20-52ce-895e-d347c1868d54
-- title:
--   Active Terminal Branch Data: support Order Contribution nil eq zero
-- statement:
--   No selected empty-start terminal branch has empty terminal order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L44-L54
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L44-L54

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_nil_eq_zero
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I [] ρ = 0 := by sorry
