-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_zero_of_followOrder_eq_none
-- name    : BKAR.Forest.boundarySupportOrderTreeFiber_eq_zero_of_followOrder_eq_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:07:34.431835+00:00
-- url     : https://prove2.me/theorems/131a2541-61d4-46d0-89d9-d455fa49edef
-- title:
--   Forest: boundary Support Order Tree Fiber eq zero of follow Order eq none
-- statement:
--   If a requested suffix cannot be followed through the selected active
--   extensions, the corresponding fixed support/order fiber is zero.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L438-L482
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L438-L482

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeFiber_eq_zero_of_followOrder_eq_none
    (choices : ActiveExtensionChoice V) :
    ∀ (order : List (Edge V)) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (I : ForestIndex V)
      (ρ : (Edge V → ℝ) → ℝ),
      followOrder? choices F order = none →
      boundarySupportOrderTreeFiber choices F pref prefixTs top I
        (pref ++ order) ρ = 0
  := by sorry
