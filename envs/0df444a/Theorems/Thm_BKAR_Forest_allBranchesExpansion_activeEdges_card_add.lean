-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesExpansion_activeEdges_card_add
-- name    : BKAR.Forest.allBranchesExpansion_activeEdges_card_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:43:44.106179+00:00
-- url     : https://prove2.me/theorems/a6b7fb23-90e8-4dce-b884-3114692bdc50
-- title:
--   Forest: all Branches Expansion active Edges card add
-- statement:
--   The exact active-edge count is a canonical terminal depth for the all-branches
--   expansion: any extra fuel beyond that depth gives the same value.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L345-L362
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L345-L362

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesExpansion_activeEdges_card_add
    (choices : ActiveExtensionChoice V) :
    ∀ (k : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      allBranchesExpansion choices (F.activeEdges.card + k)
          F pref prefixTs top ρ =
        allBranchesExpansion choices F.activeEdges.card F pref prefixTs top ρ
  := by sorry
