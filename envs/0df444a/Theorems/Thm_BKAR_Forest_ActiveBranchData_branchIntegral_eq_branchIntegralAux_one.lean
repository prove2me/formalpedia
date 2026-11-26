-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_branchIntegral_eq_branchIntegralAux_one
-- name    : BKAR.Forest.ActiveBranchData.branchIntegral_eq_branchIntegralAux_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:41:38.273089+00:00
-- url     : https://prove2.me/theorems/27ebce57-2a9d-49fb-aecc-f6539f219722
-- title:
--   Active Branch Data: branch Integral eq branch Integral Aux one
-- statement:
--   The Active Branch Data construction uses the branch Integral eq branch Integral Aux one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L130-L133
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L130-L133

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_eq_branchIntegralAux_one

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveBranchData.branchIntegral_eq_branchIntegralAux_one (data : ActiveBranchData F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ = data.branchIntegralAux 1 u ρ := by sorry
