-- Prove2me | Theorems.Thm_BKAR_Forest_cons_mem_edgeSetOrders_iff
-- name    : BKAR.Forest.cons_mem_edgeSetOrders_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:45:06.281668+00:00
-- url     : https://prove2.me/theorems/eea745a3-8950-43eb-9a79-8af250268571
-- title:
--   Forest: cons mem edge Set Orders iff
-- statement:
--   The Forest construction uses the cons mem edge Set Orders iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L151-L213
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L151-L213

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

theorem BKAR.Forest.cons_mem_edgeSetOrders_iff
    (S : Finset (Edge V)) {e : Edge V} {order : List (Edge V)} :
    e :: order ∈ edgeSetOrders S ↔
      e ∈ S ∧ order ∈ edgeSetOrders (S.erase e) := by sorry
