-- Prove2me | Theorems.Thm_FairSelling_exists_reduced
-- name    : FairSelling.exists_reduced
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:51:53.701674+00:00
-- url     : https://prove2.me/theorems/1af57d91-6831-4075-bf12-ce3ef0049748
-- title:
--   Fair Selling: exists reduced
-- statement:
--   Existence of a canonical (at most one split good) MMS partition for one valuation.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L145-L169
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L145-L169

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.exists_reduced (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g) :
    ∃ (A : Fin 2 → Finset G) (s : Finset G) (q : Fin 2 → ℝ),
      Config w p (MMS 2 w p) A s q ∧ s.card ≤ 1 := by sorry
