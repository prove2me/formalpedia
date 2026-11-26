-- Prove2me | Theorems.Thm_BKAR_Forest_paramsOfOrder_cons_self
-- name    : BKAR.Forest.paramsOfOrder_cons_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:46:08.125429+00:00
-- url     : https://prove2.me/theorems/4280a9ad-de0e-4d68-a6b1-729deadfed25
-- title:
--   Forest: params Of Order cons self
-- statement:
--   The Forest construction uses the params Of Order cons self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L463-L470
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L463-L470

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

theorem BKAR.Forest.paramsOfOrder_cons_self (F : Forest V)
    (e : Edge V) (order : List (Edge V)) (t : ℝ) (ts : List ℝ)
    (he : e ∈ F.edges) :
    F.paramsOfOrder (e :: order) (t :: ts) ⟨e, he⟩ = t := by sorry
