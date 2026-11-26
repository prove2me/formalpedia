-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_allBranchesAnalytic_empty_of_contDiff
-- name    : BKAR.BKARContDiff.allBranchesAnalytic_empty_of_contDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:21:16.449696+00:00
-- url     : https://prove2.me/theorems/b0b7b34f-3d17-4580-88b0-fefe843fbecc
-- title:
--   BKARCont Diff: all Branches Analytic empty of cont Diff
-- statement:
--   Root all-branches analytic hypothesis, discharged from `BKARContDiff`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L373-L386
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L373-L386

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.allBranchesAnalytic_empty_of_contDiff
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    Forest.allBranchesAnalytic choices (Forest.empty V).activeEdges.card
      (Forest.empty V) [] [] 1 ρ := by sorry
