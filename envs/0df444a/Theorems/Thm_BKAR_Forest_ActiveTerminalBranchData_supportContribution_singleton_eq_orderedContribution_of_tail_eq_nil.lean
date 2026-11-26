-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_singleton_eq_orderedContribution_of_tail_eq_nil
-- name    : BKAR.Forest.ActiveTerminalBranchData.supportContribution_singleton_eq_orderedContribution_of_tail_eq_nil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:29:59.462096+00:00
-- url     : https://prove2.me/theorems/8aa5dc39-91e0-555a-b23c-e3896f0c2503
-- title:
--   Active Terminal Branch Data: support Contribution singleton eq ordered Contribution of tail eq nil
-- statement:
--   If the selected branch over `a` stops after its first edge, the singleton
--   support fiber is exactly its one-edge ordered contribution.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L332-L354
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L332-L354

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

theorem BKAR.Forest.ActiveTerminalBranchData.supportContribution_singleton_eq_orderedContribution_of_tail_eq_nil
    (data : ActiveTerminalBranchData (Forest.empty V))
    (a : Edge V) (htail : (data.tail (emptyActiveEdge a)).order = [])
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution (ForestIndex.singleton a) ρ =
      (data.growth (emptyActiveEdge a)).terminal.orderedContribution [a] ρ := by sorry
