-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesExpansion_eq_boundaryExpansion_of_activeEdges_card_le
-- name    : BKAR.Forest.allBranchesExpansion_eq_boundaryExpansion_of_activeEdges_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:14:05.973413+00:00
-- url     : https://prove2.me/theorems/e41ed386-f5bf-57e1-8736-ff6913b36c4b
-- title:
--   Forest: all Branches Expansion eq boundary Expansion of active Edges card le
-- statement:
--   At any depth at least the active-edge count, the all-branches expansion has no
--   fill-parameter leaves left: it is exactly the pure boundary-sector tree.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L368-L401
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L368-L401

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesExpansion_eq_boundaryExpansion_of_activeEdges_card_le
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      allBranchesExpansion choices n F pref prefixTs top ρ =
        allBranchesBoundaryExpansion choices n F pref prefixTs top ρ
  := by sorry
