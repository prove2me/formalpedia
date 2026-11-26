-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_zero_of_followOrder_eq_none
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_eq_zero_of_followOrder_eq_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:53:19.896192+00:00
-- url     : https://prove2.me/theorems/3475e6a4-8555-5bd6-bdd0-a65c182b2a70
-- title:
--   Forest: root Boundary Support Order Contribution eq zero of follow Order eq none
-- statement:
--   A failed deterministic root order has zero contribution in every support fiber.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L597-L613
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L597-L613

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_eq_zero_of_followOrder_eq_none
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) {order : List (Edge V)}
    (horder : followOrder? choices (Forest.empty V) order = none)
    (ρ : (Edge V → ℝ) → ℝ) :
    rootBoundarySupportOrderContribution choices ρ I order = 0 := by sorry
