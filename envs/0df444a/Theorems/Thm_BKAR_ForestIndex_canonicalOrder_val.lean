-- Prove2me | Theorems.Thm_BKAR_ForestIndex_canonicalOrder_val
-- name    : BKAR.ForestIndex.canonicalOrder_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:54:41.645469+00:00
-- url     : https://prove2.me/theorems/ee94ab87-b85a-5817-b4fd-996c1d4890f9
-- title:
--   Forest Index: canonical Order val
-- statement:
--   The Forest Index construction uses the canonical Order val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L32-L34
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean#L32-L34

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.ForestIndex
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.ForestIndex.canonicalOrder_val (I : ForestIndex V) :
    I.canonicalOrder.val = I.edges.toList := by sorry

attribute [defeq] BKAR.ForestIndex.canonicalOrder_val
