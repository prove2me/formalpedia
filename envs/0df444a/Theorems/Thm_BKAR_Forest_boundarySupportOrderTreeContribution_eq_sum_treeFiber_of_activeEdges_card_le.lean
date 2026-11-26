-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeContribution_eq_sum_treeFiber_of_activeEdges_card_le
-- name    : BKAR.Forest.boundarySupportOrderTreeContribution_eq_sum_treeFiber_of_activeEdges_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:17:47.042245+00:00
-- url     : https://prove2.me/theorems/6ccde693-01dc-484c-a22f-3639ccef8a93
-- title:
--   Forest: boundary Support Order Tree Contribution eq sum tree Fiber of active Edges card le
-- statement:
--   The Forest construction uses the boundary Support Order Tree Contribution eq sum tree Fiber of active Edges card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L512-L530
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L512-L530

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeContribution_eq_sum_treeFiber_of_activeEdges_card_le
    (choices : ActiveExtensionChoice V)
    (n : Nat) (F : Forest V) (pref : List (Edge V))
    (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hle : F.activeEdges.card ≤ n)
    (hfiber :
      boundarySupportOrderTreeFiberIntegrable choices n
        F pref prefixTs top ρ) :
    boundarySupportOrderTreeContribution choices F pref prefixTs top ρ =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            boundarySupportOrderTreeFiber choices F pref prefixTs top
              I order ρ)) := by sorry
