-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_eq_sum_supportOrderContribution
-- name    : BKAR.Forest.ActiveTerminalBranchData.supportContribution_eq_sum_supportOrderContribution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:01:26.202121+00:00
-- url     : https://prove2.me/theorems/8e527578-a501-5dd8-87f8-6a0eae8ce7a4
-- title:
--   Active Terminal Branch Data: support Contribution eq sum support Order Contribution
-- statement:
--   A support contribution splits further into fixed ordered-sector fibers.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L405-L450
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L405-L450

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.supportContribution_eq_sum_supportOrderContribution
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ =
      Finset.sum (edgeSetOrders I.edges)
        (fun order => data.supportOrderContribution I order ρ) := by sorry
