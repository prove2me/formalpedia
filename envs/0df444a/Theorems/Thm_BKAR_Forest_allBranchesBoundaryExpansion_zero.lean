-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_zero
-- name    : BKAR.Forest.allBranchesBoundaryExpansion_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:57:17.371713+00:00
-- url     : https://prove2.me/theorems/7bf87169-67c4-48d4-a3b6-9c7aaaa6edc2
-- title:
--   Forest: all Branches Boundary Expansion zero
-- statement:
--   The Forest construction uses the all Branches Boundary Expansion zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L103-L110
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L103-L110

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesBoundaryExpansion_zero
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    allBranchesBoundaryExpansion choices 0 F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) := by sorry
