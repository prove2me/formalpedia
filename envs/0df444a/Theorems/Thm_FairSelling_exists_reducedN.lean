-- Prove2me | Theorems.Thm_FairSelling_exists_reducedN
-- name    : FairSelling.exists_reducedN
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:52:25.177744+00:00
-- url     : https://prove2.me/theorems/41aad563-bb38-4960-808b-54e9fe25a66f
-- title:
--   Fair Selling: exists reduced N
-- statement:
--   The Fair Selling construction uses the exists reduced N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MMSPartition.lean#L92-L104
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MMSPartition.lean#L92-L104

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.exists_reducedN (n : ℕ) (hn : 0 < n) (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g) :
    ∃ (A : Fin n → Finset G) (s : Finset G) (q : Fin n → ℝ),
      ConfigN n w p (MMS n w p) A s q ∧ s.card ≤ n - 1 := by sorry
