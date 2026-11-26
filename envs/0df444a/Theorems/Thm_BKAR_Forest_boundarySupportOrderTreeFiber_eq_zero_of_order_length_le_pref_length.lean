-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
-- name    : BKAR.Forest.boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:03:28.796023+00:00
-- url     : https://prove2.me/theorems/42daaeb6-40fb-483e-9e41-f1f7da06646b
-- title:
--   Forest: boundary Support Order Tree Fiber eq zero of order length le pref length
-- statement:
--   A support/order fiber is zero once the requested global order is no longer
--   long enough to contain the current prefix plus one more boundary edge.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L81-L144
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L81-L144

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (I : ForestIndex V)
      (order : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      order.length ≤ pref.length →
      boundarySupportOrderTreeFiber choices F pref prefixTs top
        I order ρ = 0
  := by sorry
