-- Prove2me | Theorems.Thm_BooleanFun_BV__eq_noise_operator
-- name    : BooleanFun.BV._eq_noise_operator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:08:02.131303+00:00
-- url     : https://prove2.me/theorems/ab84c102-6c77-4899-82a3-59e66fc8acb0
-- title:
--   BV: eq noise operator
-- statement:
--   One of two crucial steps in the proof of Arrow's theorem:
--    the auxiliary linear operator can be expressed in terms of `noise_operator`.
--
--   Source: https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Arrow.lean#L185-L235
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Arrow.lean#L185-L235

import Definitions.Def_BooleanFun_BooleanValued
import Definitions.Def_BooleanFun_Arrow
set_option autoImplicit false
noncomputable section
open BooleanFun BooleanFun.BV
open Classical Mathlib Finset Pi RealInnerProductSpace
variable {α : Type*} {ι : Type*}
variable {n : ℕ}
variable {f : BooleanFunc n}
local notation "T" => _Tnae3

theorem BooleanFun.BV._eq_noise_operator : T = @noise_operator n (-1/3) := by sorry
