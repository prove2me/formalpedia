-- Prove2me | Theorems.Thm_BKAR_Forest_sum_rootBoundarySupportOrderContribution_eq_sum_grownForestForSupportOrder
-- name    : BKAR.Forest.sum_rootBoundarySupportOrderContribution_eq_sum_grownForestForSupportOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:55:04.133711+00:00
-- url     : https://prove2.me/theorems/ac755c07-18bd-4d35-bddc-e2e1f7d4b665
-- title:
--   Forest: sum root Boundary Support Order Contribution eq sum grown Forest For Support Order
-- statement:
--   The Forest construction uses the sum root Boundary Support Order Contribution eq sum grown Forest For Support Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L186-L202
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L186-L202

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_rootBoundarySupportOrderContribution_eq_sum_grownForestForSupportOrder
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (edgeSetOrders I.edges)
        (fun order =>
          rootBoundarySupportOrderContribution choices ρ I order) =
      Finset.sum (edgeSetOrders I.edges).attach
        (fun order =>
          (grownForestForSupportOrder choices I order).orderedContribution
            order.val ρ) := by sorry
