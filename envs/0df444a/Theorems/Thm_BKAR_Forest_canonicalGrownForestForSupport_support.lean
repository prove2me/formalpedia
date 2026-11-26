-- Prove2me | Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_support
-- name    : BKAR.Forest.canonicalGrownForestForSupport_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:08.966041+00:00
-- url     : https://prove2.me/theorems/49d930e6-c33d-40df-b079-166d535076d4
-- title:
--   Forest: canonical Grown Forest For Support support
-- statement:
--   The Forest construction uses the canonical Grown Forest For Support support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L104-L107
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L104-L107

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.canonicalGrownForestForSupport_support
    (choices : ActiveExtensionChoice V) (I : ForestIndex V) :
    (canonicalGrownForestForSupport choices I).support = I := by sorry
