-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_standardInterp
-- name    : BKAR.Forest.ActiveBranchData.branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_standardInterp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:41.759521+00:00
-- url     : https://prove2.me/theorems/d308016a-9926-590a-9bcb-89b649534c48
-- title:
--   Active Branch Data: branch Integral Aux eq sum ordered Simplex Integral Aux mixed Partial List standard Interp
-- statement:
--   The active-branch sum in the standard terminal-interpolation form used by the
--   ordered BKAR main terms.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L227-L242
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L227-L242

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveBranchData.branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_standardInterp
    (data : ActiveBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => orderedSimplexIntegralAux top (e.val :: data.order e)
          (fun ts => mixedPartialList (e.val :: data.order e).reverse ρ
            ((data.terminal e).standardInterp
              ((data.growth e).params u ts)))) := by sorry
