-- Prove2me | Theorems.Thm_BKAR_Forest_edgeSetOrders_singleton
-- name    : BKAR.Forest.edgeSetOrders_singleton
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:07:33.207259+00:00
-- url     : https://prove2.me/theorems/6c0f94a2-90f0-4a78-9a43-7df2bf577f92
-- title:
--   Forest: edge Set Orders singleton
-- statement:
--   The Forest construction uses the edge Set Orders singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L122-L148
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L122-L148

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]

theorem BKAR.Forest.edgeSetOrders_singleton (a : Edge V) :
    edgeSetOrders ({a} : Finset (Edge V)) = {[a]} := by sorry
