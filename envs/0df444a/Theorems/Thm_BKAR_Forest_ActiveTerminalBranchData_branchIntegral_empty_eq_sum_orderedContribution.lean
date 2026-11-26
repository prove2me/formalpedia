-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegral_empty_eq_sum_orderedContribution
-- name    : BKAR.Forest.ActiveTerminalBranchData.branchIntegral_empty_eq_sum_orderedContribution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:55:17.698689+00:00
-- url     : https://prove2.me/theorems/491852f6-3d05-4b35-aba0-1f817fce8b09
-- title:
--   Active Terminal Branch Data: branch Integral empty eq sum ordered Contribution
-- statement:
--   The active-terminal branch sum from the empty forest is a finite sum of
--   canonical ordered-sector contributions, one for each selected terminal branch.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L189-L200
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L189-L200

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.branchIntegral_empty_eq_sum_orderedContribution
    (data : ActiveTerminalBranchData (Forest.empty V))
    (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      Finset.sum (Forest.empty V).activeEdges.attach
        (fun e => (data.growth e).terminal.orderedContribution
          (e.val :: (data.tail e).order) ρ) := by sorry
