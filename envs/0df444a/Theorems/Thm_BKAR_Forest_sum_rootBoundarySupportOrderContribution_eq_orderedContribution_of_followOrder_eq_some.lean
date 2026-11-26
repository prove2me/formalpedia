-- Prove2me | Theorems.Thm_BKAR_Forest_sum_rootBoundarySupportOrderContribution_eq_orderedContribution_of_followOrder_eq_some
-- name    : BKAR.Forest.sum_rootBoundarySupportOrderContribution_eq_orderedContribution_of_followOrder_eq_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:19:24.958248+00:00
-- url     : https://prove2.me/theorems/f023adb7-850c-5af6-9a00-8177d9f74c62
-- title:
--   Forest: sum root Boundary Support Order Contribution eq ordered Contribution of follow Order eq some
-- statement:
--   Deterministic finite-order form of the chosen-growth bridge: if following an
--   order through the selected active extensions reaches `G`, the support-summed
--   root fiber is exactly the ordered sector of `G` with that order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L92-L101
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L92-L101

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_rootBoundarySupportOrderContribution_eq_orderedContribution_of_followOrder_eq_some
    (choices : ActiveExtensionChoice V)
    {G : Forest V} {order : List (Edge V)}
    (hG : followOrder? choices (Forest.empty V) order = some G)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => rootBoundarySupportOrderContribution choices ρ I order) =
      G.orderedContribution order ρ := by sorry
