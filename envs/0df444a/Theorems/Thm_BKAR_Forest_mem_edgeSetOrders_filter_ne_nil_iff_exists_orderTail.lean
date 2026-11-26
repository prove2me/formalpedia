-- Prove2me | Theorems.Thm_BKAR_Forest_mem_edgeSetOrders_filter_ne_nil_iff_exists_orderTail
-- name    : BKAR.Forest.mem_edgeSetOrders_filter_ne_nil_iff_exists_orderTail
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:26:16.33135+00:00
-- url     : https://prove2.me/theorems/ce05cf36-0e3d-45cf-84eb-020708ee457a
-- title:
--   Forest: mem edge Set Orders filter ne nil iff exists order Tail
-- statement:
--   The Forest construction uses the mem edge Set Orders filter ne nil iff exists order Tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L235-L258
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L235-L258

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

theorem BKAR.Forest.mem_edgeSetOrders_filter_ne_nil_iff_exists_orderTail
    (S : Finset (Edge V)) {order : List (Edge V)} :
    order ∈ (edgeSetOrders S).filter (fun order => order ≠ []) ↔
      ∃ x ∈ edgeSetOrderTails S, x.1.val :: x.2 = order := by sorry
