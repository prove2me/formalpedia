-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_def
-- name    : BKAR.Forest.ActiveTerminalBranchData.supportContribution_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:53:55.382504+00:00
-- url     : https://prove2.me/theorems/d7f5592f-4100-4af5-8c98-0f9b4d415e66
-- title:
--   Active Terminal Branch Data: support Contribution def
-- statement:
--   The Active Terminal Branch Data construction uses the support Contribution def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L41-L50
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L41-L50

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.supportContribution_def
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = I))
        (fun e => (data.growth e).terminal.orderedContribution
          (data.growthOrder e) ρ) := by sorry
