-- Prove2me | Theorems.Thm_BooleanFun_pow_eq_self_imp
-- name    : BooleanFun.pow_eq_self_imp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:59:17.327213+00:00
-- url     : https://prove2.me/theorems/76e48d2c-42f5-43bf-a989-db331633d83d
-- title:
--   Boolean Fun: pow eq self imp
-- statement:
--   Solutions of the equation `ρᵏ = ρ` in real numbers.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L121-L135
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean#L121-L135

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_BooleanFun_Auxiliary
set_option autoImplicit false
open BooleanFun
open Finset Pi
variable {α : Type*} {β : Type*}
variable {s : Finset α}
variable {ι : Type*} [Fintype ι]
variable {κ : Type*}
variable {R : Type*} {M : Type*}
variable [Ring R] [AddCommGroup M] [Module R M]

theorem BooleanFun.pow_eq_self_imp {ρ : ℝ} {k : ℕ}:
    ρ ^ k = ρ → (k = 1 ∨ ρ = 0 ∨ ρ = 1 ∨ ρ = -1) := by sorry
