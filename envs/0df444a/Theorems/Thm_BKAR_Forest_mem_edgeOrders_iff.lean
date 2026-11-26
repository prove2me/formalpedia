-- Prove2me | Theorems.Thm_BKAR_Forest_mem_edgeOrders_iff
-- name    : BKAR.Forest.mem_edgeOrders_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:45:44.624095+00:00
-- url     : https://prove2.me/theorems/25608035-5e56-5571-a92f-948a81ac544e
-- title:
--   Forest: mem edge Orders iff
-- statement:
--   The Forest construction uses the mem edge Orders iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L362-L364
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L362-L364

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

theorem BKAR.Forest.mem_edgeOrders_iff (F : Forest V) {order : List (Edge V)} :
    order ∈ F.edgeOrders ↔ order.Perm F.edges.toList := by sorry
