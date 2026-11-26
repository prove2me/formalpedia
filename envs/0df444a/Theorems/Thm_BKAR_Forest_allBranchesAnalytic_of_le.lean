-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesAnalytic_of_le
-- name    : BKAR.Forest.allBranchesAnalytic_of_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:00:39.906391+00:00
-- url     : https://prove2.me/theorems/a4928756-32e0-4806-9b19-22b7df4c3b47
-- title:
--   Forest: all Branches Analytic of le
-- statement:
--   Analytic recursion-tree hypotheses can be truncated to a shallower depth.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L179-L196
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L179-L196

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesAnalytic_of_le
    (choices : ActiveExtensionChoice V) :
    ∀ {m n : Nat} {F : Forest V} {pref : List (Edge V)}
      {prefixTs : List ℝ} {top : ℝ} {ρ : (Edge V → ℝ) → ℝ},
      m ≤ n →
      allBranchesAnalytic choices n F pref prefixTs top ρ →
      allBranchesAnalytic choices m F pref prefixTs top ρ
  := by sorry
