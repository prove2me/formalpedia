-- Prove2me | Theorems.Thm_BKAR_Forest_mem_edgeOrders_iff_toFinset_eq_and_nodup
-- name    : BKAR.Forest.mem_edgeOrders_iff_toFinset_eq_and_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:45:29.886431+00:00
-- url     : https://prove2.me/theorems/45ef9a22-388c-41dd-9576-5f5634d6b9b6
-- title:
--   Forest: mem edge Orders iff to Finset eq and nodup
-- statement:
--   The Forest construction uses the mem edge Orders iff to Finset eq and nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L370-L373
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L370-L373

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

theorem BKAR.Forest.mem_edgeOrders_iff_toFinset_eq_and_nodup
    (F : Forest V) {order : List (Edge V)} :
    order ∈ F.edgeOrders ↔ order.toFinset = F.edges ∧ order.Nodup := by sorry
