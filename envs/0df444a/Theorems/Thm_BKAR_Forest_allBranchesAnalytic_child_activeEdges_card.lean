-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesAnalytic_child_activeEdges_card
-- name    : BKAR.Forest.allBranchesAnalytic.child_activeEdges_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:01:09.105827+00:00
-- url     : https://prove2.me/theorems/0440182d-f8d6-5c24-ada6-96309a804bb6
-- title:
--   all Branches Analytic: child active Edges card
-- statement:
--   The exact-depth child analytic hypothesis contained in `allBranchesAnalytic`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L76-L101
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L76-L101

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesAnalytic.child_activeEdges_card
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ)
    {t : ℝ} (ht : t ∈ Set.uIcc 0 top) :
    allBranchesAnalytic choices
      (choices F e).forest.activeEdges.card
      (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ := by sorry
