-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_growth_branchIntegrand_eq_mixedPartialList_standardInterp
-- name    : BKAR.Forest.ActiveBranchData.growth_branchIntegrand_eq_mixedPartialList_standardInterp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:33.594346+00:00
-- url     : https://prove2.me/theorems/7a3bf145-a432-5de7-a826-5957571a06f3
-- title:
--   Active Branch Data: growth branch Integrand eq mixed Partial List standard Interp
-- statement:
--   The selected branch integrand in its standard terminal-interpolation form.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L213-L221
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L213-L221

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

theorem BKAR.Forest.ActiveBranchData.growth_branchIntegrand_eq_mixedPartialList_standardInterp
    (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (ts : List ℝ) :
    (data.growth e).branchIntegrand u ρ ts =
      mixedPartialList (e.val :: data.order e).reverse ρ
        ((data.terminal e).standardInterp ((data.growth e).params u ts)) := by sorry
