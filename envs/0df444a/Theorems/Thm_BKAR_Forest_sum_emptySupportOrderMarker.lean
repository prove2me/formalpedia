-- Prove2me | Theorems.Thm_BKAR_Forest_sum_emptySupportOrderMarker
-- name    : BKAR.Forest.sum_emptySupportOrderMarker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:17:59.455866+00:00
-- url     : https://prove2.me/theorems/3343ea7b-6bf3-5de9-86e7-f0c5ddbdb11f
-- title:
--   Forest: sum empty Support Order Marker
-- statement:
--   The Forest construction uses the sum empty Support Order Marker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L690-L712
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L690-L712

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_emptySupportOrderMarker
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            if I.edges = ∅ ∧ order = [] then ρ zeroConfig else 0)) =
      ρ zeroConfig := by sorry
