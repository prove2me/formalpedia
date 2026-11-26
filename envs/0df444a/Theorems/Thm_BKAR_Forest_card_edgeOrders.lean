-- Prove2me | Theorems.Thm_BKAR_Forest_card_edgeOrders
-- name    : BKAR.Forest.card_edgeOrders
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:26:39.92087+00:00
-- url     : https://prove2.me/theorems/3ee8e8df-b54b-5578-ab56-c1394f66c7af
-- title:
--   Forest: card edge Orders
-- statement:
--   The Forest construction uses the card edge Orders property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L390-L392
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L390-L392

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

theorem BKAR.Forest.card_edgeOrders (F : Forest V) :
    F.edgeOrders.card = F.edges.card.factorial := by sorry
