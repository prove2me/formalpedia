-- Prove2me | Theorems.Thm_FairChores_delta_iff_EF_of_cbar_eq_price
-- name    : FairChores.delta_iff_EF_of_cbar_eq_price
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:22:27.787104+00:00
-- url     : https://prove2.me/theorems/4140582d-98e8-43a6-bc32-1b60c90e30ae
-- title:
--   Fair Chores: delta iff EF of cbar eq price
-- statement:
--   If the effective cost of `t` is its market price, the delta condition is precisely the
--   envy-free condition.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L182-L186
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L182-L186

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {ci p : T → ℝ}
omit [Fintype T] [DecidableEq T]

theorem FairChores.delta_iff_EF_of_cbar_eq_price {Bi Bj : Finset T} {t : T} (h : cbar ci p t = p t) :
    (p t - cbar ci p t ≥ cbarSum ci p Bi - cbarSum ci p Bj) ↔
      cbarSum ci p Bi ≤ cbarSum ci p Bj := by sorry
