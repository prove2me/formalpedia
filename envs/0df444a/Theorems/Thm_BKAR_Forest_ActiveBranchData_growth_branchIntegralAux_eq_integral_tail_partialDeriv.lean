-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_growth_branchIntegralAux_eq_integral_tail_partialDeriv
-- name    : BKAR.Forest.ActiveBranchData.growth_branchIntegralAux_eq_integral_tail_partialDeriv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:21:38.256308+00:00
-- url     : https://prove2.me/theorems/9f941317-51c4-4ef9-921a-8536d9dfde16
-- title:
--   Active Branch Data: growth branch Integral Aux eq integral tail partial Deriv
-- statement:
--   The Active Branch Data construction uses the growth branch Integral Aux eq integral tail partial Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L112-L121
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L112-L121

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveBranchData.growth_branchIntegralAux_eq_integral_tail_partialDeriv
    (data : ActiveBranchData F) (e : {e // e ∈ F.activeEdges})
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (data.growth e).branchIntegralAux top u ρ =
      ∫ t in 0..top,
        (data.tail e).branchIntegralAux t
          ((data.extension e).extension.extendParam u t)
          (partialDeriv e.val ρ) := by sorry
