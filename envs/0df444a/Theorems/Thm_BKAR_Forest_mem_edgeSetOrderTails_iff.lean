-- Prove2me | Theorems.Thm_BKAR_Forest_mem_edgeSetOrderTails_iff
-- name    : BKAR.Forest.mem_edgeSetOrderTails_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:45:19.703804+00:00
-- url     : https://prove2.me/theorems/80c75767-867b-4a6a-9ee3-5f68866a3875
-- title:
--   Forest: mem edge Set Order Tails iff
-- statement:
--   The Forest construction uses the mem edge Set Order Tails iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L222-L232
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L222-L232

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

theorem BKAR.Forest.mem_edgeSetOrderTails_iff
    (S : Finset (Edge V))
    {x : Σ _ : {y : Edge V // y ∈ S}, List (Edge V)} :
    x ∈ edgeSetOrderTails S ↔
      x.2 ∈ edgeSetOrders (S.erase x.1.val) := by sorry
