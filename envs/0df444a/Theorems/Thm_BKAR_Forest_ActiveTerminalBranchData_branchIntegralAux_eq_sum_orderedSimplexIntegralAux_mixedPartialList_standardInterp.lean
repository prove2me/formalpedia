-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_standardInterp
-- name    : BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_standardInterp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:25:36.44682+00:00
-- url     : https://prove2.me/theorems/f7af8316-5e10-4569-a89b-316cb83daab6
-- title:
--   Active Terminal Branch Data: branch Integral Aux eq sum ordered Simplex Integral Aux mixed Partial List standard Interp
-- statement:
--   The active-terminal branch sum in the standard interpolation form used by the
--   ordered BKAR main terms.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L522-L532
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L522-L532

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_Forest_ActiveBranchData_branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_standardInterp
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_standardInterp
    (data : ActiveTerminalBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => orderedSimplexIntegralAux top (e.val :: (data.tail e).order)
          (fun ts => mixedPartialList (e.val :: (data.tail e).order).reverse ρ
            ((data.tail e).terminal.standardInterp
              ((data.growth e).growth.params u ts)))) := by sorry
