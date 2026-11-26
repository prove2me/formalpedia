-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_zero_of_not_exists_pref_append
-- name    : BKAR.Forest.boundarySupportOrderTreeFiber_eq_zero_of_not_exists_pref_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:06:33.421814+00:00
-- url     : https://prove2.me/theorems/96efeed0-4c85-4c14-844a-dfa6ad19a6bd
-- title:
--   Forest: boundary Support Order Tree Fiber eq zero of not exists pref append
-- statement:
--   A support/order fiber can only contribute along branches whose accumulated
--   prefix is still a prefix of the requested global order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L133-L196
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L133-L196

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeFiber_eq_zero_of_not_exists_pref_append
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (I : ForestIndex V)
      (order : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      (¬ ∃ tail : List (Edge V), pref ++ tail = order) →
      boundarySupportOrderTreeFiber choices F pref prefixTs top
        I order ρ = 0
  := by sorry
