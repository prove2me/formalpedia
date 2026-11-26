-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_eq_activeEdges_card_of_card_le
-- name    : BKAR.Forest.allBranchesBoundaryExpansion_eq_activeEdges_card_of_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:14:14.172729+00:00
-- url     : https://prove2.me/theorems/0af2b664-9bf3-5065-b668-ffbe9f7ade30
-- title:
--   Forest: all Branches Boundary Expansion eq active Edges card of card le
-- statement:
--   Collapse any sufficiently deep boundary tree to exact active depth.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L479-L489
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L479-L489

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesBoundaryExpansion_eq_activeEdges_card_of_card_le
    (choices : ActiveExtensionChoice V)
    (n : Nat) (F : Forest V) (pref : List (Edge V))
    (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hle : F.activeEdges.card ≤ n) :
    allBranchesBoundaryExpansion choices n F pref prefixTs top ρ =
      allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ := by sorry
