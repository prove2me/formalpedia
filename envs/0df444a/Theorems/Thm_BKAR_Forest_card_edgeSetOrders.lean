-- Prove2me | Theorems.Thm_BKAR_Forest_card_edgeSetOrders
-- name    : BKAR.Forest.card_edgeSetOrders
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:46:29.926364+00:00
-- url     : https://prove2.me/theorems/50bb2695-7e42-5255-811e-ef630d7d4f6e
-- title:
--   Forest: card edge Set Orders
-- statement:
--   The Forest construction uses the card edge Set Orders property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L72-L77
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L72-L77

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

theorem BKAR.Forest.card_edgeSetOrders (S : Finset (Edge V)) :
    (edgeSetOrders S).card = S.card.factorial := by sorry
