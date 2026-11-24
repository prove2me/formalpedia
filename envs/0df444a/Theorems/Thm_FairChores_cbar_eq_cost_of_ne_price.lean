-- Prove2me | Theorems.Thm_FairChores_cbar_eq_cost_of_ne_price
-- name    : FairChores.cbar_eq_cost_of_ne_price
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:22:26.233878+00:00
-- url     : https://prove2.me/theorems/eb686e6d-c2ed-4888-9c10-3d087e8eae37
-- title:
--   Fair Chores: cbar eq cost of ne price
-- statement:
--   If the effective cost of `t` is not its market price, it is the in-house cost, so the
--   delta condition takes the manuscript's form `p(t) − cᵢ(t) ≥ c̄ᵢ(Bᵢ) − c̄ᵢ(B_j)`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L191-L194
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L191-L194

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {ci p : T → ℝ}
omit [Fintype T] [DecidableEq T]

theorem FairChores.cbar_eq_cost_of_ne_price {t : T} (h : cbar ci p t ≠ p t) : cbar ci p t = ci t := by sorry
