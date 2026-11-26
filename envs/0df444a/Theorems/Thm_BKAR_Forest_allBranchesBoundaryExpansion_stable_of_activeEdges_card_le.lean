-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_stable_of_activeEdges_card_le
-- name    : BKAR.Forest.allBranchesBoundaryExpansion_stable_of_activeEdges_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:14:10.370464+00:00
-- url     : https://prove2.me/theorems/21c069f3-4899-5a30-890f-f44ed0a392fd
-- title:
--   Forest: all Branches Boundary Expansion stable of active Edges card le
-- statement:
--   The pure boundary-sector tree also stabilizes once the remaining depth
--   dominates the active-edge count.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L418-L455
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L418-L455

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesBoundaryExpansion_stable_of_activeEdges_card_le
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      allBranchesBoundaryExpansion choices (n + 1) F pref prefixTs top ρ =
        allBranchesBoundaryExpansion choices n F pref prefixTs top ρ
  := by sorry
