-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_intervalIntegrable_of_order_length_le_pref_length
-- name    : BKAR.Forest.boundarySupportOrderTreeFiber_intervalIntegrable_of_order_length_le_pref_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:17:22.134269+00:00
-- url     : https://prove2.me/theorems/06c87742-28cd-4f20-ab90-f73573ed7e60
-- title:
--   Forest: boundary Support Order Tree Fiber interval Integrable of order length le pref length
-- statement:
--   The Forest construction uses the boundary Support Order Tree Fiber interval Integrable of order length le pref length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L155-L174
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L155-L174

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeFiber_intervalIntegrable_of_order_length_le_pref_length
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ)
    (hlen : order.length ≤ pref.length) :
    IntervalIntegrable
      (fun t : ℝ =>
        boundarySupportOrderTreeFiber choices F pref prefixTs t I order ρ)
      MeasureTheory.volume 0 top := by sorry
