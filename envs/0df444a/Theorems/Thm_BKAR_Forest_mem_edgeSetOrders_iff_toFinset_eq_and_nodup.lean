-- Prove2me | Theorems.Thm_BKAR_Forest_mem_edgeSetOrders_iff_toFinset_eq_and_nodup
-- name    : BKAR.Forest.mem_edgeSetOrders_iff_toFinset_eq_and_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:44:39.686322+00:00
-- url     : https://prove2.me/theorems/18cbe90b-fd39-52ed-948b-546428fa71d1
-- title:
--   Forest: mem edge Set Orders iff to Finset eq and nodup
-- statement:
--   The Forest construction uses the mem edge Set Orders iff to Finset eq and nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L37-L55
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L37-L55

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

theorem BKAR.Forest.mem_edgeSetOrders_iff_toFinset_eq_and_nodup
    (S : Finset (Edge V)) {order : List (Edge V)} :
    order ∈ edgeSetOrders S ↔ order.toFinset = S ∧ order.Nodup := by sorry
