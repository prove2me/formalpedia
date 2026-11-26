-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_singleton_eq_zero_of_tail_ne_nil
-- name    : BKAR.Forest.ActiveTerminalBranchData.supportContribution_singleton_eq_zero_of_tail_ne_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:30:05.366172+00:00
-- url     : https://prove2.me/theorems/78e01331-0305-5713-8fb8-8c99d61a0dfd
-- title:
--   Active Terminal Branch Data: support Contribution singleton eq zero of tail ne nil
-- statement:
--   If the selected branch over `a` has a nonempty tail, then it contributes
--   nothing to the singleton support fiber over `{a}`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L360-L375
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L360-L375

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

theorem BKAR.Forest.ActiveTerminalBranchData.supportContribution_singleton_eq_zero_of_tail_ne_nil
    (data : ActiveTerminalBranchData (Forest.empty V))
    (a : Edge V) (htail : (data.tail (emptyActiveEdge a)).order ≠ [])
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution (ForestIndex.singleton a) ρ = 0 := by sorry
