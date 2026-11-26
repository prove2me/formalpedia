-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportContribution_singleton_eq_sum_first_eq_and_tail_nil
-- name    : BKAR.Forest.ActiveTerminalBranchData.supportContribution_singleton_eq_sum_first_eq_and_tail_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:54:41.721852+00:00
-- url     : https://prove2.me/theorems/430e779d-f339-55da-882a-6c9e7ee1c7a5
-- title:
--   Active Terminal Branch Data: support Contribution singleton eq sum first eq and tail nil
-- statement:
--   Singleton-support terminal branch fibers can be read as the branches with the
--   specified first edge and empty tail order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L308-L326
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L308-L326

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

theorem BKAR.Forest.ActiveTerminalBranchData.supportContribution_singleton_eq_sum_first_eq_and_tail_nil
    (data : ActiveTerminalBranchData (Forest.empty V))
    (a : Edge V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution (ForestIndex.singleton a) ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e => e.val = a ∧ (data.tail e).order = []))
        (fun e => (data.growth e).terminal.orderedContribution
          (data.growthOrder e) ρ) := by sorry
