-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_growth_terminal_orderedSectorSum_eq_sum_orderTails_emptyStart
-- name    : BKAR.Forest.ActiveTerminalBranchData.growth_terminal_orderedSectorSum_eq_sum_orderTails_emptyStart
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:29:04.735513+00:00
-- url     : https://prove2.me/theorems/8eef2379-900d-5b0e-85b0-cb45aa9a496e
-- title:
--   Active Terminal Branch Data: growth terminal ordered Sector Sum eq sum order Tails empty Start
-- statement:
--   Each selected terminal forest admits the same first-edge/tail ordered-sector
--   decomposition as any nonempty forest.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L174-L183
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean#L174-L183

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Support_Growth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.growth_terminal_orderedSectorSum_eq_sum_orderTails_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (ρ : (Edge V → ℝ) → ℝ) :
    (data.growth e).terminal.orderedSectorSum ρ =
      Finset.sum (edgeSetOrderTails (data.growth e).terminal.edges)
        (fun x => (data.growth e).terminal.orderedContribution
          (x.1.val :: x.2) ρ) := by sorry
