-- Prove2me | Theorems.Thm_BKAR_Forest_edgeSetOrders_filter_ne_nil_eq_self_of_nonempty
-- name    : BKAR.Forest.edgeSetOrders_filter_ne_nil_eq_self_of_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:45:29.863153+00:00
-- url     : https://prove2.me/theorems/f4657592-1fe6-4f66-980e-e7d966b8a90e
-- title:
--   Forest: edge Set Orders filter ne nil eq self of nonempty
-- statement:
--   The Forest construction uses the edge Set Orders filter ne nil eq self of nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L328-L344
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L328-L344

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

theorem BKAR.Forest.edgeSetOrders_filter_ne_nil_eq_self_of_nonempty
    {S : Finset (Edge V)} (hS : S.Nonempty) :
    (edgeSetOrders S).filter (fun order => order ≠ []) = edgeSetOrders S := by sorry
