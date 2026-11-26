-- Prove2me | Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_edges
-- name    : BKAR.Forest.canonicalGrownForestForSupport_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:55:31.593128+00:00
-- url     : https://prove2.me/theorems/992ab85f-65d0-453c-84c6-5f0cb1ca57ff
-- title:
--   Forest: canonical Grown Forest For Support edges
-- statement:
--   The Forest construction uses the canonical Grown Forest For Support edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L109-L112
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L109-L112

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.canonicalGrownForestForSupport_edges
    (choices : ActiveExtensionChoice V) (I : ForestIndex V) :
    (canonicalGrownForestForSupport choices I).edges = I.edges := by sorry
