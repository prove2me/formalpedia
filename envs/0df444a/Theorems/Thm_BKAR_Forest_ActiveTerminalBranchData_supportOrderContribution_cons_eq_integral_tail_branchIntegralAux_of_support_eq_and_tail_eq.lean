-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_supportOrderContribution_cons_eq_integral_tail_branchIntegralAux_of_support_eq_and_tail_eq
-- name    : BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_cons_eq_integral_tail_branchIntegralAux_of_support_eq_and_tail_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:29:39.41046+00:00
-- url     : https://prove2.me/theorems/c940fc8b-d291-5bf5-9c4c-5032ef30ddc9
-- title:
--   Active Terminal Branch Data: support Order Contribution cons eq integral tail branch Integral Aux of support eq and tail eq
-- statement:
--   Recursive form of a fixed nonempty support/order fiber: once the selected
--   branch over the head edge has the requested support and tail order, the fiber
--   is exactly the tail branch integral after the first edge.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L98-L115
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean#L98-L115

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

theorem BKAR.Forest.ActiveTerminalBranchData.supportOrderContribution_cons_eq_integral_tail_branchIntegralAux_of_support_eq_and_tail_eq
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (a : Edge V) (tail : List (Edge V))
    (hsupport : (data.growth (emptyActiveEdge a)).support = I)
    (htail : (data.tail (emptyActiveEdge a)).order = tail)
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I (a :: tail) ρ =
      ∫ t in 0..(1 : ℝ),
        (data.tail (emptyActiveEdge a)).branchIntegralAux t
          ((data.extension (emptyActiveEdge a)).extension.extendParam
            emptyParam t)
          (partialDeriv a ρ) := by sorry
