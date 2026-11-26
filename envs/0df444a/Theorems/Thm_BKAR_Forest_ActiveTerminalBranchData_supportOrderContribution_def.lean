-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportOrderContribution_def
-- name    : BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:53:42.996402+00:00
-- url     : https://prove2.me/theorems/62cdb143-76a2-5940-b251-b5f2ac3a55c3
-- title:
--   Active Terminal Branch Data: support Order Contribution def
-- statement:
--   The Active Terminal Branch Data construction uses the support Order Contribution def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L68-L78
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Contribution.lean#L68-L78

import Definitions.Def_BKAR_CubePartition_Support_Growth
import Definitions.Def_BKAR_CubePartition_Support_Contribution
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_def
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I order ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = I ∧
            data.growthOrder e = order))
        (fun e => (data.growth e).terminal.orderedContribution order ρ) := by sorry
