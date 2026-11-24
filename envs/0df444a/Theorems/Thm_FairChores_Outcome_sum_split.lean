-- Prove2me | Theorems.Thm_FairChores_Outcome_sum_split
-- name    : FairChores.Outcome.sum_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:47:25.4228+00:00
-- url     : https://prove2.me/theorems/f72f4aca-728b-4791-9fb0-d0e2a3ef1a83
-- title:
--   Outcome: sum split
-- statement:
--   In a feasible outcome, every chore is either outsourced or performed by exactly one
--   agent, so any additive quantity splits accordingly.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L120-L130
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresModel.lean#L120-L130

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}

theorem FairChores.Outcome.sum_split {o : Outcome T n} (hvalid : o.Valid p) (f : T → ℝ) :
    ∑ t, f t = (∑ t ∈ o.outsourced, f t) + ∑ j, ∑ t ∈ o.kept j, f t := by sorry
