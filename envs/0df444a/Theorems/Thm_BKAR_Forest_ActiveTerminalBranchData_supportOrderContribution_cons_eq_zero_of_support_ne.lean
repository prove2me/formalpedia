-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportOrderContribution_cons_eq_zero_of_support_ne
-- name    : BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_cons_eq_zero_of_support_ne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:29:43.012063+00:00
-- url     : https://prove2.me/theorems/8f3f2ef4-3b04-53e0-8dca-f49e7fb12f71
-- title:
--   Active Terminal Branch Data: support Order Contribution cons eq zero of support ne
-- statement:
--   If the branch over the head edge does not have support `I`, then no branch
--   can contribute to the ordered sector `a :: tail` over `I`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L121-L138
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L121-L138

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_cons_eq_zero_of_support_ne
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (a : Edge V) (tail : List (Edge V))
    (hsupport : (data.growth (emptyActiveEdge a)).support ≠ I)
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I (a :: tail) ρ = 0 := by sorry
