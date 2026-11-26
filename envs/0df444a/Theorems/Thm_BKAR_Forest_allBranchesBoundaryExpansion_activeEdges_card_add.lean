-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_activeEdges_card_add
-- name    : BKAR.Forest.allBranchesBoundaryExpansion_activeEdges_card_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:14:16.135717+00:00
-- url     : https://prove2.me/theorems/ac7c96f8-b8ca-573b-a0d6-542227096f99
-- title:
--   Forest: all Branches Boundary Expansion active Edges card add
-- statement:
--   Extra boundary-tree fuel beyond active depth gives the same value.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L458-L476
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L458-L476

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesBoundaryExpansion_activeEdges_card_add
    (choices : ActiveExtensionChoice V) :
    ∀ (k : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      allBranchesBoundaryExpansion choices (F.activeEdges.card + k)
          F pref prefixTs top ρ =
        allBranchesBoundaryExpansion choices F.activeEdges.card
          F pref prefixTs top ρ
  := by sorry
