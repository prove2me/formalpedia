-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_branchIntegral_eq_sum_orderedSimplexIntegral_mixedPartialList_standardInterp
-- name    : BKAR.Forest.ActiveBranchData.branchIntegral_eq_sum_orderedSimplexIntegral_mixedPartialList_standardInterp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:21:53.438193+00:00
-- url     : https://prove2.me/theorems/a0fcda9d-277f-4e0d-93a8-caae16706708
-- title:
--   Active Branch Data: branch Integral eq sum ordered Simplex Integral mixed Partial List standard Interp
-- statement:
--   Unit-simplex version of
--   `ActiveBranchData.branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_standardInterp`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L248-L258
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L248-L258

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

theorem BKAR.Forest.ActiveBranchData.branchIntegral_eq_sum_orderedSimplexIntegral_mixedPartialList_standardInterp
    (data : ActiveBranchData F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => orderedSimplexIntegral (e.val :: data.order e)
          (fun ts => mixedPartialList (e.val :: data.order e).reverse ρ
            ((data.terminal e).standardInterp
              ((data.growth e).params u ts)))) := by sorry
