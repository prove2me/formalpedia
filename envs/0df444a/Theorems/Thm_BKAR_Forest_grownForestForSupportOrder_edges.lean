-- Prove2me | Theorems.Thm_BKAR_Forest_grownForestForSupportOrder_edges
-- name    : BKAR.Forest.grownForestForSupportOrder_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:55:29.212802+00:00
-- url     : https://prove2.me/theorems/c06f9677-fcce-543a-87e8-c000e317f056
-- title:
--   Forest: grown Forest For Support Order edges
-- statement:
--   The Forest construction uses the grown Forest For Support Order edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L74-L81
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L74-L81

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.grownForestForSupportOrder_edges
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges}) :
    (grownForestForSupportOrder choices I order).edges = I.edges := by sorry
