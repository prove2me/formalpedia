-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesExpansion_succ_of_activeEdges_eq_empty
-- name    : BKAR.Forest.allBranchesExpansion_succ_of_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:14:04.409772+00:00
-- url     : https://prove2.me/theorems/b6c823b7-602b-5750-85e1-4d44bf3c7d81
-- title:
--   Forest: all Branches Expansion succ of active Edges eq empty
-- statement:
--   Once a node has no active edges, every positive all-branches level is just its
--   boundary ordered-sector term.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L286-L298
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L286-L298

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesExpansion_succ_of_activeEdges_eq_empty
    (choices : ActiveExtensionChoice V) (n : Nat)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hF : F.activeEdges = ∅) :
    allBranchesExpansion choices (n + 1) F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) := by sorry
