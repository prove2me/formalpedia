-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesAnalytic_zero
-- name    : BKAR.Forest.allBranchesAnalytic_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:04:59.569607+00:00
-- url     : https://prove2.me/theorems/e2c197f6-670a-58f7-b29f-6d57822cdee7
-- title:
--   Forest: all Branches Analytic zero
-- statement:
--   The Forest construction uses the all Branches Analytic zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L171-L176
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L171-L176

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesAnalytic_zero
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    allBranchesAnalytic choices 0 F pref prefixTs top ρ := by sorry
