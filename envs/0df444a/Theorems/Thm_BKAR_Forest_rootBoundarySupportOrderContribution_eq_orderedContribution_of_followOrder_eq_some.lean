-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_orderedContribution_of_followOrder_eq_some
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_eq_orderedContribution_of_followOrder_eq_some
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:08:00.900459+00:00
-- url     : https://prove2.me/theorems/7a246845-57d6-464f-b8ae-45126cc18f27
-- title:
--   Forest: root Boundary Support Order Contribution eq ordered Contribution of follow Order eq some
-- statement:
--   Root fiber bridge stated in terms of the deterministic order follower.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L585-L594
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L585-L594

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_eq_orderedContribution_of_followOrder_eq_some
    (choices : ActiveExtensionChoice V)
    {G : Forest V} {order : List (Edge V)}
    (hG : followOrder? choices (Forest.empty V) order = some G)
    (ρ : (Edge V → ℝ) → ℝ)
    (horder : order ≠ []) :
    rootBoundarySupportOrderContribution choices ρ G.support order =
      G.orderedContribution order ρ := by sorry
