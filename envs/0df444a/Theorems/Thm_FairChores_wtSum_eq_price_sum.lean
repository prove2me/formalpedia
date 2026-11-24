-- Prove2me | Theorems.Thm_FairChores_wtSum_eq_price_sum
-- name    : FairChores.wtSum_eq_price_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:18:40.406179+00:00
-- url     : https://prove2.me/theorems/afe8f043-be6c-4d5d-9315-d679bfcc6997
-- title:
--   Fair Chores: wt Sum eq price sum
-- statement:
--   If every chore of `R` is expensive for the agent, its weight is the market price.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagFilling.lean#L45-L48
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresBagFilling.lean#L45-L48

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresBagLemma
import Definitions.Def_RequestProject_ChoresBagFilling
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {mu : Fin n → ℝ}
omit [Fintype T] [DecidableEq T]

theorem FairChores.wtSum_eq_price_sum {i : Fin n} {R : Finset T} (h : ∀ t ∈ R, mu i < cbar (c i) p t) :
    wtSum (c i) p (mu i) R = ∑ t ∈ R, p t := by sorry
