-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeContribution_eq_sum_supportOrderPairs_treeFiber_of_activeEdges_card_le
-- name    : BKAR.Forest.boundarySupportOrderTreeContribution_eq_sum_supportOrderPairs_treeFiber_of_activeEdges_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:17:46.722928+00:00
-- url     : https://prove2.me/theorems/1b11eb9f-2c5d-448a-ab97-1c9335f3eefe
-- title:
--   Forest: boundary Support Order Tree Contribution eq sum support Order Pairs tree Fiber of active Edges card le
-- statement:
--   The folded boundary tree is the finite sum of its global support/order fibers.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L411-L510
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L411-L510

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeContribution_eq_sum_supportOrderPairs_treeFiber_of_activeEdges_card_le
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      boundarySupportOrderTreeFiberIntegrable choices n
        F pref prefixTs top ρ →
      boundarySupportOrderTreeContribution choices F pref prefixTs top ρ =
        Finset.sum (supportOrderPairs V)
          (fun x =>
            boundarySupportOrderTreeFiber choices F pref prefixTs top
              x.1 x.2 ρ)
  := by sorry
