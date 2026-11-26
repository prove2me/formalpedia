-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_singleton_branchIntegral_eq_activeBranchData_singleton
-- name    : BKAR.Forest.ActiveTerminalBranchData.singleton_branchIntegral_eq_activeBranchData_singleton
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:25:20.305541+00:00
-- url     : https://prove2.me/theorems/8aca5834-8dcc-541f-b5b5-2c29cb0d41e5
-- title:
--   Active Terminal Branch Data: singleton branch Integral eq active Branch Data singleton
-- statement:
--   The Active Terminal Branch Data construction uses the singleton branch Integral eq active Branch Data singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L481-L489
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L481-L489

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.singleton_branchIntegral_eq_activeBranchData_singleton
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (singleton extensions hterm).branchIntegral u ρ =
      (ActiveBranchData.singleton extensions).branchIntegral u ρ := by sorry
