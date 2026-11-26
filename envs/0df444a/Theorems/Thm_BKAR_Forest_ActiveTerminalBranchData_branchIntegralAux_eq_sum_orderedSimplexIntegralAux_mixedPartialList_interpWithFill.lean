-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_interpWithFill
-- name    : BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_interpWithFill
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:25:39.61555+00:00
-- url     : https://prove2.me/theorems/dc39f391-d165-4dec-9b4f-18d09bce639e
-- title:
--   Active Terminal Branch Data: branch Integral Aux eq sum ordered Simplex Integral Aux mixed Partial List interp With Fill
-- statement:
--   Terminal fill-parameter form of the active-terminal branch sum.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L537-L547
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L537-L547

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_interpWithFill
    (data : ActiveTerminalBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (b : ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => orderedSimplexIntegralAux top (e.val :: (data.tail e).order)
          (fun ts => mixedPartialList (e.val :: (data.tail e).order).reverse ρ
            ((data.tail e).terminal.interpWithFill
              ((data.growth e).growth.params u ts) b))) := by sorry
