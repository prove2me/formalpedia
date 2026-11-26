-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_intervalIntegrable_of_support_edges_eq_empty
-- name    : BKAR.Forest.boundarySupportOrderTreeFiber_intervalIntegrable_of_support_edges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:48:08.162378+00:00
-- url     : https://prove2.me/theorems/f15b62a1-e34b-5413-b0c3-4bfe1403bec8
-- title:
--   Forest: boundary Support Order Tree Fiber interval Integrable of support edges eq empty
-- statement:
--   The Forest construction uses the boundary Support Order Tree Fiber interval Integrable of support edges eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L176-L195
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L176-L195

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeFiber_intervalIntegrable_of_support_edges_eq_empty
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ)
    (hI : I.edges = ∅)
    (horder : order ∈ edgeSetOrders I.edges) :
    IntervalIntegrable
      (fun t : ℝ =>
        boundarySupportOrderTreeFiber choices F pref prefixTs t I order ρ)
      MeasureTheory.volume 0 top := by sorry
