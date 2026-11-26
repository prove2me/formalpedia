-- Prove2me | Theorems.Thm_BKAR_Forest_eq_and_tail_eq_nil_of_cons_toFinset_eq_singleton_of_nodup
-- name    : BKAR.Forest.eq_and_tail_eq_nil_of_cons_toFinset_eq_singleton_of_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:47:18.323707+00:00
-- url     : https://prove2.me/theorems/b2e04da8-21de-4cc4-b4d2-c0320c8beda6
-- title:
--   Forest: eq and tail eq nil of cons to Finset eq singleton of nodup
-- statement:
--   The Forest construction uses the eq and tail eq nil of cons to Finset eq singleton of nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L96-L119
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean#L96-L119

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]

theorem BKAR.Forest.eq_and_tail_eq_nil_of_cons_toFinset_eq_singleton_of_nodup
    {e a : Edge V} {tail : List (Edge V)}
    (hset : (e :: tail).toFinset = ({a} : Finset (Edge V)))
    (hnodup : (e :: tail).Nodup) :
    e = a ∧ tail = [] := by sorry
