-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_singleton_branchIntegral_empty_eq_sum_orderedContribution
-- name    : BKAR.Forest.ActiveTerminalBranchData.singleton_branchIntegral_empty_eq_sum_orderedContribution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:30:11.246829+00:00
-- url     : https://prove2.me/theorems/7d340dc1-bb15-5053-bc7e-bbada1a5679d
-- title:
--   Active Terminal Branch Data: singleton branch Integral empty eq sum ordered Contribution
-- statement:
--   For singleton terminal branches from the empty forest, the active-terminal
--   branch sum is a finite sum of canonical one-edge ordered-sector contributions.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L381-L398
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L381-L398

import Definitions.Def_BKAR_CubePartition_Support_Contribution
import Definitions.Def_BKAR_CubePartition_Support_Terminal
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.singleton_branchIntegral_empty_eq_sum_orderedContribution
    (extensions :
      ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
        ActiveExtension (Forest.empty V) e.val)
    (hterm :
      ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
        (extensions e).forest.activeEdges = ∅)
    (ρ : (Edge V → ℝ) → ℝ) :
    (singleton extensions hterm).branchIntegral emptyParam ρ =
      Finset.sum (Forest.empty V).activeEdges.attach
        (fun e => (extensions e).forest.orderedContribution [e.val] ρ) := by sorry
