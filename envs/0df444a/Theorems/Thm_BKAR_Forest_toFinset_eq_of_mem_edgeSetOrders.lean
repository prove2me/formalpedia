-- Prove2me | Theorems.Thm_BKAR_Forest_toFinset_eq_of_mem_edgeSetOrders
-- name    : BKAR.Forest.toFinset_eq_of_mem_edgeSetOrders
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:45:03.623878+00:00
-- url     : https://prove2.me/theorems/de0f63ab-e66e-5dd9-a4aa-1f5289fbb6e2
-- title:
--   Forest: to Finset eq of mem edge Set Orders
-- statement:
--   The Forest construction uses the to Finset eq of mem edge Set Orders property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L58-L62
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L58-L62

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

theorem BKAR.Forest.toFinset_eq_of_mem_edgeSetOrders
    {S : Finset (Edge V)} {order : List (Edge V)}
    (h : order ∈ edgeSetOrders S) :
    order.toFinset = S := by sorry
