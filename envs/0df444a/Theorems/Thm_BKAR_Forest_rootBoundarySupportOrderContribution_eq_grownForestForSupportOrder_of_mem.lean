-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder_of_mem
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:32.132239+00:00
-- url     : https://prove2.me/theorems/2c082276-0b31-4b0e-b13b-0388aa728cf1
-- title:
--   Forest: root Boundary Support Order Contribution eq grown Forest For Support Order of mem
-- statement:
--   The Forest construction uses the root Boundary Support Order Contribution eq grown Forest For Support Order of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L175-L184
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L175-L184

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder_of_mem
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) {order : List (Edge V)}
    (horder : order ∈ edgeSetOrders I.edges)
    (ρ : (Edge V → ℝ) → ℝ) :
    rootBoundarySupportOrderContribution choices ρ I order =
      (grownForestForSupportOrder choices I ⟨order, horder⟩).orderedContribution
        order ρ := by sorry
