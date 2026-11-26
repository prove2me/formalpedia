-- Prove2me | Theorems.Thm_BKAR_Forest_standardInterp_paramsOfOrder_eq_of_edges_eq
-- name    : BKAR.Forest.standardInterp_paramsOfOrder_eq_of_edges_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:09:22.924896+00:00
-- url     : https://prove2.me/theorems/542a4ff7-f95a-4799-aa3f-ab8e0e7dfce0
-- title:
--   Forest: standard Interp params Of Order eq of edges eq
-- statement:
--   In a common edge order, `paramsOfOrder` gives the same standard interpolation
--   point for any two `Forest` representatives with the same underlying edge set.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L449-L457
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L449-L457

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

theorem BKAR.Forest.standardInterp_paramsOfOrder_eq_of_edges_eq
    (F G : Forest V) (hedges : F.edges = G.edges)
    (order : List (Edge V)) (ts : List ℝ) :
    F.standardInterp (F.paramsOfOrder order ts) =
      G.standardInterp (G.paramsOfOrder order ts) := by sorry
