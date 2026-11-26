-- Prove2me | Theorems.Thm_BKAR_Forest_sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber_filter_edges_ne_empty
-- name    : BKAR.Forest.sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber_filter_edges_ne_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:05:57.726806+00:00
-- url     : https://prove2.me/theorems/95727b8a-196a-4bc3-b92b-3b6920c613e2
-- title:
--   Forest: sum root Boundary Support Order Contribution eq zero Config add sum tree Fiber filter edges ne empty
-- statement:
--   The Forest construction uses the sum root Boundary Support Order Contribution eq zero Config add sum tree Fiber filter edges ne empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L750-L796
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L750-L796

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber_filter_edges_ne_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            rootBoundarySupportOrderContribution choices ρ I order)) =
      ρ zeroConfig +
        Finset.sum
          ((Finset.univ : Finset (ForestIndex V)).filter
            (fun I => I.edges ≠ ∅))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
                I order ρ)) := by sorry
