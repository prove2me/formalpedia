-- Prove2me | Theorems.Thm_BKAR_Forest_sum_rootBoundarySupportOrderContribution_eq_zero_of_followOrder_eq_none
-- name    : BKAR.Forest.sum_rootBoundarySupportOrderContribution_eq_zero_of_followOrder_eq_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:54:19.095307+00:00
-- url     : https://prove2.me/theorems/6b8d7055-b79c-55f3-b7bd-b49046a4a7e2
-- title:
--   Forest: sum root Boundary Support Order Contribution eq zero of follow Order eq none
-- statement:
--   Complementary deterministic finite-order form: if the selected extensions
--   cannot follow the requested root order, then that fixed order has zero total
--   root fiber after summing over supports.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L108-L129
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L108-L129

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_rootBoundarySupportOrderContribution_eq_zero_of_followOrder_eq_none
    (choices : ActiveExtensionChoice V)
    {order : List (Edge V)}
    (horder : followOrder? choices (Forest.empty V) order = none)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => rootBoundarySupportOrderContribution choices ρ I order) =
      0 := by sorry
