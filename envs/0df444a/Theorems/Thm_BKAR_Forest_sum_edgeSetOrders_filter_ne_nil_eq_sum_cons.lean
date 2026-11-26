-- Prove2me | Theorems.Thm_BKAR_Forest_sum_edgeSetOrders_filter_ne_nil_eq_sum_cons
-- name    : BKAR.Forest.sum_edgeSetOrders_filter_ne_nil_eq_sum_cons
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:47:14.474282+00:00
-- url     : https://prove2.me/theorems/a10f0bd7-ec1e-5d6d-b48d-a4c801ebb089
-- title:
--   Forest: sum edge Set Orders filter ne nil eq sum cons
-- statement:
--   The Forest construction uses the sum edge Set Orders filter ne nil eq sum cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L278-L325
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L278-L325

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

theorem BKAR.Forest.sum_edgeSetOrders_filter_ne_nil_eq_sum_cons
    {β : Type*} [AddCommMonoid β]
    (S : Finset (Edge V)) (φ : List (Edge V) → β) :
    Finset.sum ((edgeSetOrders S).filter (fun order => order ≠ []))
        (fun ord => φ ord) =
      Finset.sum S.attach
        (fun e => Finset.sum (edgeSetOrders (S.erase e.val))
          (fun ord => φ (e.val :: ord))) := by sorry
