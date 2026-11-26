-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportOrderContribution_cons_eq_zero_of_tail_ne
-- name    : BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_cons_eq_zero_of_tail_ne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:29:46.6643+00:00
-- url     : https://prove2.me/theorems/7bace855-4c13-5c40-b1f2-676ad7efcc41
-- title:
--   Active Terminal Branch Data: support Order Contribution cons eq zero of tail ne
-- statement:
--   If the branch over the head edge has a different tail order, then it does not
--   contribute to the ordered sector `a :: tail`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L144-L164
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L144-L164

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

theorem BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_cons_eq_zero_of_tail_ne
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (a : Edge V) (tail : List (Edge V))
    (htail : (data.tail (emptyActiveEdge a)).order ≠ tail)
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I (a :: tail) ρ = 0 := by sorry
