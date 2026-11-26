-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegral_eq_branchIntegralAux_one
-- name    : BKAR.Forest.ActiveTerminalBranchData.branchIntegral_eq_branchIntegralAux_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:47:07.2814+00:00
-- url     : https://prove2.me/theorems/e357a8c4-2cb1-459b-b2c6-7d8ab7e8e67e
-- title:
--   Active Terminal Branch Data: branch Integral eq branch Integral Aux one
-- statement:
--   The Active Terminal Branch Data construction uses the branch Integral eq branch Integral Aux one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L465-L469
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L465-L469

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_ActiveBranchData_branchIntegral_eq_branchIntegralAux_one
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_eq_branchIntegralAux_one

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.branchIntegral_eq_branchIntegralAux_one
    (data : ActiveTerminalBranchData F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ = data.branchIntegralAux 1 u ρ := by sorry
