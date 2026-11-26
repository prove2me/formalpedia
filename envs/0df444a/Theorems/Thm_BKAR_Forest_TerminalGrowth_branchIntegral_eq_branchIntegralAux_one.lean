-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_eq_branchIntegralAux_one
-- name    : BKAR.Forest.TerminalGrowth.branchIntegral_eq_branchIntegralAux_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:46:44.336309+00:00
-- url     : https://prove2.me/theorems/b1ea1bc6-8b68-5cf8-8a3a-b4f6ce21a8f0
-- title:
--   Terminal Growth: branch Integral eq branch Integral Aux one
-- statement:
--   The Terminal Growth construction uses the branch Integral eq branch Integral Aux one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L63-L66
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L63-L66

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_ActiveBranchData_branchIntegral_eq_branchIntegralAux_one
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_eq_branchIntegralAux_one

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.branchIntegral_eq_branchIntegralAux_one (data : TerminalGrowth F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ = data.branchIntegralAux 1 u ρ := by sorry
