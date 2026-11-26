-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_growth_branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
-- name    : BKAR.Forest.ActiveBranchData.growth_branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:36:33.040873+00:00
-- url     : https://prove2.me/theorems/e49c5de0-3dee-4bd1-993d-903674dc1189
-- title:
--   Active Branch Data: growth branch Integrand eq mixed Partial List interp With Fill of active Edges eq empty
-- statement:
--   For a terminal selected branch, its integrand may be read on the terminal
--   fill-parameter interpolation point.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L196-L208
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L196-L208

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

theorem BKAR.Forest.ActiveBranchData.growth_branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
    (data : ActiveBranchData F)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (data.terminal e).activeEdges = ∅)
    (e : {e // e ∈ F.activeEdges})
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (ts : List ℝ) (b : ℝ) :
    (data.growth e).branchIntegrand u ρ ts =
      mixedPartialList (e.val :: data.order e).reverse ρ
        ((data.terminal e).interpWithFill
          ((data.growth e).params u ts) b) := by sorry
