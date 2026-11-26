-- Prove2me | Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_support
-- name    : BKAR.Forest.grownForestForSupportOrder_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:55:42.272861+00:00
-- url     : https://prove2.me/theorems/7071125d-0d5a-4267-b082-0aba34ac3319
-- title:
--   Forest: grown Forest For Support Order support
-- statement:
--   The Forest construction uses the grown Forest For Support Order support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L65-L72
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L65-L72

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.grownForestForSupportOrder_support
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges}) :
    (grownForestForSupportOrder choices I order).support = I := by sorry
