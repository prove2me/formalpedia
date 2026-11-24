-- Prove2me | Theorems.Thm_FairSelling_reduce_to_nsub1
-- name    : FairSelling.reduce_to_nsub1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:52:22.023823+00:00
-- url     : https://prove2.me/theorems/0d039ee7-fbe6-4f83-b38a-34d42ad7606e
-- title:
--   Fair Selling: reduce to nsub1
-- statement:
--   The Fair Selling construction uses the reduce to nsub1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MMSPartition.lean#L74-L86
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MMSPartition.lean#L74-L86

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.reduce_to_nsub1 (n : ℕ) (hn : 0 < n) (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (r : ℝ) :
    ∀ (k : ℕ) (A : Fin n → Finset G) (s : Finset G) (q : Fin n → ℝ),
      ConfigN n w p r A s q → s.card ≤ k →
      ∃ (A' : Fin n → Finset G) (s' : Finset G) (q' : Fin n → ℝ),
        ConfigN n w p r A' s' q' ∧ s'.card ≤ n - 1 := by sorry
