-- Prove2me | Theorems.Thm_BKAR_Forest_paramsOfOrder_empty
-- name    : BKAR.Forest.paramsOfOrder_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:45:33.050906+00:00
-- url     : https://prove2.me/theorems/c17569cd-c3eb-40cc-941c-d1d10a126270
-- title:
--   Forest: params Of Order empty
-- statement:
--   The Forest construction uses the params Of Order empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L459-L461
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L459-L461

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

theorem BKAR.Forest.paramsOfOrder_empty (order : List (Edge V)) (ts : List ℝ) :
    (Forest.empty V).paramsOfOrder order ts = emptyParam := by sorry
