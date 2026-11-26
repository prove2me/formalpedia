-- Prove2me | Theorems.Thm_BKAR_Forest_sum_edgeOrders_eq_sum_cons_of_edges_nonempty
-- name    : BKAR.Forest.sum_edgeOrders_eq_sum_cons_of_edges_nonempty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:47:28.140177+00:00
-- url     : https://prove2.me/theorems/7b838c81-cda6-52b6-86e0-dea9fc467ed0
-- title:
--   Forest: sum edge Orders eq sum cons of edges nonempty
-- statement:
--   The Forest construction uses the sum edge Orders eq sum cons of edges nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L409-L416
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L409-L416

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

theorem BKAR.Forest.sum_edgeOrders_eq_sum_cons_of_edges_nonempty
    {β : Type*} [AddCommMonoid β] (F : Forest V)
    (hF : F.edges.Nonempty) (φ : List (Edge V) → β) :
    Finset.sum F.edgeOrders (fun order => φ order) =
      Finset.sum F.edges.attach
        (fun e => Finset.sum (edgeSetOrders (F.edges.erase e.val))
          (fun order => φ (e.val :: order))) := by sorry
