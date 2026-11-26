-- Prove2me | Theorems.Thm_BKAR_Forest_mem_edgeSetOrders_iff
-- name    : BKAR.Forest.mem_edgeSetOrders_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:45:09.852433+00:00
-- url     : https://prove2.me/theorems/31787006-24c9-4b32-8272-b3f643a21ab7
-- title:
--   Forest: mem edge Set Orders iff
-- statement:
--   The Forest construction uses the mem edge Set Orders iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L31-L34
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L31-L34

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

theorem BKAR.Forest.mem_edgeSetOrders_iff (S : Finset (Edge V))
    {order : List (Edge V)} :
    order ∈ edgeSetOrders S ↔ order.Perm S.toList := by sorry
