-- Prove2me | Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_order_mem_edgeOrders
-- name    : BKAR.Forest.canonicalGrownForestForSupport_order_mem_edgeOrders
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:55:09.253147+00:00
-- url     : https://prove2.me/theorems/eaaeb4f5-dd54-539d-a48e-7b40536865ec
-- title:
--   Forest: canonical Grown Forest For Support order mem edge Orders
-- statement:
--   The Forest construction uses the canonical Grown Forest For Support order mem edge Orders property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L114-L122
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L114-L122

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.canonicalGrownForestForSupport_order_mem_edgeOrders
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    {order : List (Edge V)} (horder : order ∈ edgeSetOrders I.edges) :
    order ∈ (canonicalGrownForestForSupport choices I).edgeOrders := by sorry
