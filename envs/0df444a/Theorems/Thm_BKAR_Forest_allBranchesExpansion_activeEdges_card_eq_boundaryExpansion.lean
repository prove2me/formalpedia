-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesExpansion_activeEdges_card_eq_boundaryExpansion
-- name    : BKAR.Forest.allBranchesExpansion_activeEdges_card_eq_boundaryExpansion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:58:22.269608+00:00
-- url     : https://prove2.me/theorems/eca378f7-a08c-5910-97c2-a9fe06f3cf51
-- title:
--   Forest: all Branches Expansion active Edges card eq boundary Expansion
-- statement:
--   Exact active-depth terminalization of the all-branches expansion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L404-L412
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L404-L412

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesExpansion_activeEdges_card_eq_boundaryExpansion
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    allBranchesExpansion choices F.activeEdges.card F pref prefixTs top ρ =
      allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ := by sorry
