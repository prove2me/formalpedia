-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegral_empty_eq_sum_growthOrderContribution
-- name    : BKAR.Forest.ActiveTerminalBranchData.branchIntegral_empty_eq_sum_growthOrderContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:55:29.551969+00:00
-- url     : https://prove2.me/theorems/ea44465b-3f14-4ba1-961d-4515ca2102bd
-- title:
--   Active Terminal Branch Data: branch Integral empty eq sum growth Order Contribution
-- statement:
--   Version of `ActiveTerminalBranchData.branchIntegral_empty_eq_sum_orderedContribution`
--   using the packaged terminal edge order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L206-L216
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L206-L216

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.branchIntegral_empty_eq_sum_growthOrderContribution
    (data : ActiveTerminalBranchData (Forest.empty V))
    (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      Finset.sum (Forest.empty V).activeEdges.attach
        (fun e => (data.growth e).terminal.orderedContribution
          (data.growthOrder e) ρ) := by sorry
