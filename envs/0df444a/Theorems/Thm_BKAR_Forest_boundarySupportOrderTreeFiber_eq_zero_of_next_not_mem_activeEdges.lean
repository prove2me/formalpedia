-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_zero_of_next_not_mem_activeEdges
-- name    : BKAR.Forest.boundarySupportOrderTreeFiber_eq_zero_of_next_not_mem_activeEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:19:24.400558+00:00
-- url     : https://prove2.me/theorems/353f9fa6-06f0-4b2f-98cc-5669d1ca65cd
-- title:
--   Forest: boundary Support Order Tree Fiber eq zero of next not mem active Edges
-- statement:
--   If the next requested edge is not active, the whole fiber is zero.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L379-L432
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L379-L432

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeFiber_eq_zero_of_next_not_mem_activeEdges
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (I : ForestIndex V)
    (e₀ : Edge V) (tail : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ)
    (he₀ : e₀ ∉ F.activeEdges) :
    boundarySupportOrderTreeFiber choices F pref prefixTs top I
        (pref ++ e₀ :: tail) ρ = 0 := by sorry
