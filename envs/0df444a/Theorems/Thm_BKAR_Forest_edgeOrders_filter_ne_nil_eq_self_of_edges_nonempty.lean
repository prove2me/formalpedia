-- Prove2me | Theorems.Thm_BKAR_Forest_edgeOrders_filter_ne_nil_eq_self_of_edges_nonempty
-- name    : BKAR.Forest.edgeOrders_filter_ne_nil_eq_self_of_edges_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:26:56.040084+00:00
-- url     : https://prove2.me/theorems/198c31c2-47b4-45f5-b7e5-c915d28b4f4f
-- title:
--   Forest: edge Orders filter ne nil eq self of edges nonempty
-- statement:
--   The Forest construction uses the edge Orders filter ne nil eq self of edges nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L404-L407
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L404-L407

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

theorem BKAR.Forest.edgeOrders_filter_ne_nil_eq_self_of_edges_nonempty
    (F : Forest V) (hF : F.edges.Nonempty) :
    F.edgeOrders.filter (fun order => order ≠ []) = F.edgeOrders := by sorry
