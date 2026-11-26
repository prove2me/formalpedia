-- Prove2me | Theorems.Thm_BKAR_Forest_sum_edgeSetOrders_eq_sum_cons_of_nonempty
-- name    : BKAR.Forest.sum_edgeSetOrders_eq_sum_cons_of_nonempty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:47:51.579543+00:00
-- url     : https://prove2.me/theorems/988657a4-9ec6-4d7f-9e26-516ef482946c
-- title:
--   Forest: sum edge Set Orders eq sum cons of nonempty
-- statement:
--   The Forest construction uses the sum edge Set Orders eq sum cons of nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L347-L356
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L347-L356

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

theorem BKAR.Forest.sum_edgeSetOrders_eq_sum_cons_of_nonempty
    {β : Type*} [AddCommMonoid β]
    {S : Finset (Edge V)} (hS : S.Nonempty)
    (φ : List (Edge V) → β) :
    Finset.sum (edgeSetOrders S) (fun order => φ order) =
      Finset.sum S.attach
        (fun e => Finset.sum (edgeSetOrders (S.erase e.val))
          (fun order => φ (e.val :: order))) := by sorry
