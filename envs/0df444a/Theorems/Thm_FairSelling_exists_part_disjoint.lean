-- Prove2me | Theorems.Thm_FairSelling_exists_part_disjoint
-- name    : FairSelling.exists_part_disjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:07:48.010812+00:00
-- url     : https://prove2.me/theorems/337a5cd1-3b5c-4676-8eb3-84309b844b6a
-- title:
--   Fair Selling: exists part disjoint
-- statement:
--   If at most two goods are removed, one of the three parts of a configuration is untouched.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L51-L65
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ConfigSplit.lean#L51-L65

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]

theorem FairSelling.exists_part_disjoint (A : Fin 3 → Finset G)
    (hA : ∀ i j : Fin 3, i ≠ j → Disjoint (A i) (A j))
    (X : Finset G) (hX : X.card ≤ 2) : ∃ j : Fin 3, Disjoint (A j) X := by sorry
