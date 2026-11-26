-- Prove2me | Theorems.Thm_BKAR_Forest_toList_mem_edgeOrders
-- name    : BKAR.Forest.toList_mem_edgeOrders
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:26:30.067921+00:00
-- url     : https://prove2.me/theorems/56d2c7f3-5005-4cda-aeb8-357af9d355e8
-- title:
--   Forest: to List mem edge Orders
-- statement:
--   The Forest construction uses the to List mem edge Orders property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L366-L368
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L366-L368

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

theorem BKAR.Forest.toList_mem_edgeOrders (F : Forest V) :
    F.edges.toList ∈ F.edgeOrders := by sorry
