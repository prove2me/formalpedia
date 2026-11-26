-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesExpansion_stable_of_activeEdges_card_le
-- name    : BKAR.Forest.allBranchesExpansion_stable_of_activeEdges_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:14:02.021063+00:00
-- url     : https://prove2.me/theorems/fafe0ba5-871c-5bfb-9166-6f040deda56f
-- title:
--   Forest: all Branches Expansion stable of active Edges card le
-- statement:
--   Once the remaining depth dominates the number of active edges at a node, adding
--   one more all-branches layer does not change the expansion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L304-L339
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L304-L339

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesExpansion_stable_of_activeEdges_card_le
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      allBranchesExpansion choices (n + 1) F pref prefixTs top ρ =
        allBranchesExpansion choices n F pref prefixTs top ρ
  := by sorry
