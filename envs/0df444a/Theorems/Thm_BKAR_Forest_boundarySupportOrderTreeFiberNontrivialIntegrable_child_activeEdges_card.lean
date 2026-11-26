-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiberNontrivialIntegrable_child_activeEdges_card
-- name    : BKAR.Forest.boundarySupportOrderTreeFiberNontrivialIntegrable.child_activeEdges_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:49:14.715842+00:00
-- url     : https://prove2.me/theorems/c0afe430-37a0-55c1-a4d1-1279fe6055de
-- title:
--   boundary Support Order Tree Fiber Nontrivial Integrable: child active Edges card
-- statement:
--   The exact-depth child nontrivial fiber-integrability hypothesis contained in
--   the parent exact-depth hypothesis.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L308-L335
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L308-L335

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Theorems.Thm_BKAR_Forest_allBranchesAnalytic_child_activeEdges_card

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeFiberNontrivialIntegrable.child_activeEdges_card
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hfiber :
      boundarySupportOrderTreeFiberNontrivialIntegrable choices
        F.activeEdges.card F pref prefixTs top ρ)
    {t : ℝ} (ht : t ∈ Set.uIcc 0 top) :
    boundarySupportOrderTreeFiberNontrivialIntegrable choices
      (choices F e).forest.activeEdges.card
      (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ := by sorry
