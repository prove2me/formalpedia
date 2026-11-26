-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
-- name    : BKAR.Forest.ActiveBranchData.branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:42:15.351378+00:00
-- url     : https://prove2.me/theorems/c5918b87-6b53-511d-8eaf-e6a4bdf0aa49
-- title:
--   Active Branch Data: branch Integral Aux eq sum ordered Simplex Integral Aux mixed Partial List interp With Fill of active Edges eq empty
-- statement:
--   Terminal selected branches rewrite the active-branch sum as a sum of ordered
--   simplex integrals over terminal fill-parameter interpolation points.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L264-L283
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L264-L283

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

theorem BKAR.Forest.ActiveBranchData.branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
    (data : ActiveBranchData F)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (data.terminal e).activeEdges = ∅)
    (top : ℝ) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => orderedSimplexIntegralAux top (e.val :: data.order e)
          (fun ts => mixedPartialList (e.val :: data.order e).reverse ρ
            ((data.terminal e).interpWithFill
              ((data.growth e).params u ts) b))) := by sorry
