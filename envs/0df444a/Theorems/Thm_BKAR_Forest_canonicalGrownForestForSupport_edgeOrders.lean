-- Prove2me | Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_edgeOrders
-- name    : BKAR.Forest.canonicalGrownForestForSupport_edgeOrders
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:33.034406+00:00
-- url     : https://prove2.me/theorems/f2de5368-2508-4ba3-b88e-1ae700582bbc
-- title:
--   Forest: canonical Grown Forest For Support edge Orders
-- statement:
--   The Forest construction uses the canonical Grown Forest For Support edge Orders property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L124-L131
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L124-L131

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.canonicalGrownForestForSupport_edgeOrders
    (choices : ActiveExtensionChoice V) (I : ForestIndex V) :
    (canonicalGrownForestForSupport choices I).edgeOrders =
      edgeSetOrders I.edges := by sorry
