-- Prove2me | Theorems.Thm_FairSelling_exists_class_subseq
-- name    : FairSelling.exists_class_subseq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:53:36.905624+00:00
-- url     : https://prove2.me/theorems/0498f1d5-4c11-4e88-86ce-e0ffdcaf954e
-- title:
--   Fair Selling: exists class subseq
-- statement:
--   Any sequence of outcomes has a subsequence along which the *class* (the set of sold goods and
--   the assignment of the kept goods) is constant.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L66-L86
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L66-L86

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.exists_class_subseq (o : ℕ → Outcome G n) :
    ∃ (S : Finset G) (A : Fin n → Finset G) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ k, (o (φ k)).sold = S) ∧ (∀ k, (o (φ k)).kept = A) := by sorry
