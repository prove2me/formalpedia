-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum
-- name    : BKAR.Forest.allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:57:22.839234+00:00
-- url     : https://prove2.me/theorems/8f0fb2ec-1ac2-5a11-9f72-bf90c26ad9ab
-- title:
--   Forest: all Branches Boundary Expansion active Edges card eq standard add sum
-- statement:
--   Exact-depth unfolding of the boundary-sector tree. Each recursive child is
--   already evaluated at its own exact active depth.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L495-L539
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L495-L539

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            allBranchesBoundaryExpansion choices
              (choices F e).forest.activeEdges.card
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t ρ) := by sorry
