-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_integral_child_of_tail_ne_nil
-- name    : BKAR.Forest.boundarySupportOrderTreeFiber_eq_integral_child_of_tail_ne_nil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:05:45.671628+00:00
-- url     : https://prove2.me/theorems/44e7a3bf-10d8-57e0-83d6-6153735a4861
-- title:
--   Forest: boundary Support Order Tree Fiber eq integral child of tail ne nil
-- statement:
--   If the requested order continues with a nonempty tail after the next edge,
--   then the tree fiber follows exactly the child indexed by that next edge.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L320-L376
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L320-L376

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeFiber_eq_integral_child_of_tail_ne_nil
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (I : ForestIndex V)
    (e₀ : Edge V) (tail : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ)
    (he₀ : e₀ ∈ F.activeEdges)
    (htail : tail ≠ []) :
    boundarySupportOrderTreeFiber choices F pref prefixTs top I
        (pref ++ e₀ :: tail) ρ =
      ∫ t in 0..top,
        boundarySupportOrderTreeFiber choices
          (choices F ⟨e₀, he₀⟩).forest (pref ++ [e₀])
          (prefixTs ++ [t]) t I (pref ++ e₀ :: tail) ρ := by sorry
