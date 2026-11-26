-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegral_empty_eq_sum_supportContribution
-- name    : BKAR.Forest.ActiveTerminalBranchData.branchIntegral_empty_eq_sum_supportContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:54:32.748477+00:00
-- url     : https://prove2.me/theorems/81274f74-9c2a-5690-8db5-7aa98b3f0f49
-- title:
--   Active Terminal Branch Data: branch Integral empty eq sum support Contribution
-- statement:
--   The selected active-terminal branches from the empty forest can be regrouped by
--   their finite terminal forest support.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L84-L109
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L84-L109

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.branchIntegral_empty_eq_sum_supportContribution
    (data : ActiveTerminalBranchData (Forest.empty V))
    (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => data.supportContribution I ρ) := by sorry
