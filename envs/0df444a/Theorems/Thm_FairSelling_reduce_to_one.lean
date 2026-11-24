-- Prove2me | Theorems.Thm_FairSelling_reduce_to_one
-- name    : FairSelling.reduce_to_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:49.755053+00:00
-- url     : https://prove2.me/theorems/138738ad-11fc-4468-954f-40fa6fc0c60b
-- title:
--   Fair Selling: reduce to one
-- statement:
--   Iterating `reduce_step` we reach a configuration with at most one split good.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L126-L142
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L126-L142

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.reduce_to_one (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (r : ℝ) :
    ∀ (k : ℕ) (A : Fin 2 → Finset G) (s : Finset G) (q : Fin 2 → ℝ),
      Config w p r A s q → s.card ≤ k →
      ∃ (A' : Fin 2 → Finset G) (s' : Finset G) (q' : Fin 2 → ℝ),
        Config w p r A' s' q' ∧ s'.card ≤ 1 := by sorry
