-- Prove2me | Theorems.Thm_FairSelling_reduce_stepN
-- name    : FairSelling.reduce_stepN
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:52:16.215629+00:00
-- url     : https://prove2.me/theorems/5bb8eac3-9a10-4a4f-b58d-e9619cb4564d
-- title:
--   Fair Selling: reduce step N
-- statement:
--   The Fair Selling construction uses the reduce step N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MMSPartition.lean#L41-L69
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MMSPartition.lean#L41-L69

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.reduce_stepN (n : ℕ) (hn : 0 < n) (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (r : ℝ)
    (A : Fin n → Finset G) (s : Finset G) (q : Fin n → ℝ)
    (hcfg : ConfigN n w p r A s q) (hcard : n ≤ s.card) :
    ∃ (A' : Fin n → Finset G) (s' : Finset G) (q' : Fin n → ℝ),
      ConfigN n w p r A' s' q' ∧ s'.card < s.card := by sorry
