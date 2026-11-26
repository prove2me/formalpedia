-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_emptyStart_eq_orderedContribution
-- name    : BKAR.Forest.TerminalGrowth.branchIntegral_emptyStart_eq_orderedContribution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:46:40.496917+00:00
-- url     : https://prove2.me/theorems/28fb2a66-f726-5418-abeb-f0e7536ead8e
-- title:
--   Terminal Growth: branch Integral empty Start eq ordered Contribution
-- statement:
--   An empty-start terminal branch integral is the canonical ordered-sector
--   contribution of its terminal forest and terminal edge order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L121-L128
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L121-L128

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.branchIntegral_emptyStart_eq_orderedContribution
    (data : TerminalGrowth (Forest.empty V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      data.terminal.orderedContribution data.order ρ := by sorry
