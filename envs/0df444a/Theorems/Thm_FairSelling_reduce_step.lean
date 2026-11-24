-- Prove2me | Theorems.Thm_FairSelling_reduce_step
-- name    : FairSelling.reduce_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:47.301583+00:00
-- url     : https://prove2.me/theorems/75453148-c35b-47b5-b569-1db9ee63d4fd
-- title:
--   Fair Selling: reduce step
-- statement:
--   One reduction step: if the split set has at least two goods, we may move one of them into a
--   group, strictly decreasing the number of split goods while preserving all `Config` properties.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L45-L123
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L45-L123

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.reduce_step (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (r : ℝ)
    (A : Fin 2 → Finset G) (s : Finset G) (q : Fin 2 → ℝ)
    (hcfg : Config w p r A s q) (hcard : 2 ≤ s.card) :
    ∃ (A' : Fin 2 → Finset G) (s' : Finset G) (q' : Fin 2 → ℝ),
      Config w p r A' s' q' ∧ s'.card < s.card := by sorry
