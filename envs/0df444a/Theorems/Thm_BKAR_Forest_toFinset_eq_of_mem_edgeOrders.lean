-- Prove2me | Theorems.Thm_BKAR_Forest_toFinset_eq_of_mem_edgeOrders
-- name    : BKAR.Forest.toFinset_eq_of_mem_edgeOrders
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:47:20.304662+00:00
-- url     : https://prove2.me/theorems/38c16e10-5b7a-554a-b583-253935f0172c
-- title:
--   Forest: to Finset eq of mem edge Orders
-- statement:
--   The Forest construction uses the to Finset eq of mem edge Orders property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L375-L378
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L375-L378

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

theorem BKAR.Forest.toFinset_eq_of_mem_edgeOrders (F : Forest V)
    {order : List (Edge V)} (h : order ∈ F.edgeOrders) :
    order.toFinset = F.edges := by sorry
