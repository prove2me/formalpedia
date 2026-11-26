-- Prove2me | Theorems.Thm_BKAR_Forest_cons_mem_edgeOrders_iff
-- name    : BKAR.Forest.cons_mem_edgeOrders_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:45:13.568803+00:00
-- url     : https://prove2.me/theorems/e9bc1779-8fda-51cd-a769-3792e1724bbc
-- title:
--   Forest: cons mem edge Orders iff
-- statement:
--   The Forest construction uses the cons mem edge Orders iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L398-L402
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L398-L402

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

theorem BKAR.Forest.cons_mem_edgeOrders_iff (F : Forest V)
    {e : Edge V} {order : List (Edge V)} :
    e :: order ∈ F.edgeOrders ↔
      e ∈ F.edges ∧ order ∈ edgeSetOrders (F.edges.erase e) := by sorry
