-- Prove2me | Theorems.Thm_BKAR_Forest_paramValue_paramsOfOrder_eq_of_edges_eq
-- name    : BKAR.Forest.paramValue_paramsOfOrder_eq_of_edges_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:47:32.488127+00:00
-- url     : https://prove2.me/theorems/5710bf62-946e-5ce4-a364-2202fa1025d2
-- title:
--   Forest: param Value params Of Order eq of edges eq
-- statement:
--   The Forest construction uses the param Value params Of Order eq of edges eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L427-L443
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L427-L443

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

theorem BKAR.Forest.paramValue_paramsOfOrder_eq_of_edges_eq
    (F G : Forest V) (hedges : F.edges = G.edges)
    (order : List (Edge V)) (ts : List ℝ) (e : Edge V) :
    F.paramValue (F.paramsOfOrder order ts) e =
      G.paramValue (G.paramsOfOrder order ts) e := by sorry
