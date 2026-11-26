-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_succ
-- name    : BKAR.Forest.allBranchesBoundaryExpansion_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:57:21.263373+00:00
-- url     : https://prove2.me/theorems/f1baf913-bc88-53a0-8b5d-eeeb973a08a9
-- title:
--   Forest: all Branches Boundary Expansion succ
-- statement:
--   The Forest construction uses the all Branches Boundary Expansion succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L112-L123
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L112-L123

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesBoundaryExpansion_succ
    (choices : ActiveExtensionChoice V) (n : Nat)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    allBranchesBoundaryExpansion choices (n + 1) F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            allBranchesBoundaryExpansion choices n (choices F e).forest
              (pref ++ [e.val]) (prefixTs ++ [t]) t ρ) := by sorry
