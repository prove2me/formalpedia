-- Prove2me | Theorems.Thm_BKAR_Forest_paramsOfOrder_cons_of_ne
-- name    : BKAR.Forest.paramsOfOrder_cons_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:45:53.862608+00:00
-- url     : https://prove2.me/theorems/14dfb53b-dc7e-5368-b50b-396c51786048
-- title:
--   Forest: params Of Order cons of ne
-- statement:
--   The Forest construction uses the params Of Order cons of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L472-L481
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L472-L481

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

theorem BKAR.Forest.paramsOfOrder_cons_of_ne (F : Forest V)
    {e e' : Edge V} (order : List (Edge V)) (t : ℝ) (ts : List ℝ)
    (he' : e' ∈ F.edges) (hne : e' ≠ e) :
    F.paramsOfOrder (e :: order) (t :: ts) ⟨e', he'⟩ =
      ts.getD (order.idxOf e') 0 := by sorry
