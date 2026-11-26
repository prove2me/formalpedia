-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegral_empty_eq_sum_supportOrderContribution
-- name    : BKAR.Forest.ActiveTerminalBranchData.branchIntegral_empty_eq_sum_supportOrderContribution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:01:37.074144+00:00
-- url     : https://prove2.me/theorems/735ab867-0476-58a7-a1b3-4a2a7bf68c86
-- title:
--   Active Terminal Branch Data: branch Integral empty eq sum support Order Contribution
-- statement:
--   The full empty-start terminal branch sum is indexed by support and then by one
--   of the canonical ordered sectors of that support.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L456-L466
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L456-L466

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.branchIntegral_empty_eq_sum_supportOrderContribution
    (data : ActiveTerminalBranchData (Forest.empty V))
    (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order => data.supportOrderContribution I order ρ)) := by sorry
