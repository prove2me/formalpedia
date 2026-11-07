-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_sum_weight_mul_chi
-- name    : AaronsonAmbainis.Row.sum_weight_mul_chi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:56:53.176973+00:00
-- url     : https://prove2.me/theorems/4fe350a4-9250-4fb6-a83a-7e45c411f75b
-- title:
--   Row: sum weight mul chi
-- statement:
--   The `weight u`-average of the character `chi T` is `∏_{i ∈ T} u_i`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Extension.lean#L31-L45
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Extension.lean#L31-L45

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Extension
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Row.sum_weight_mul_chi (u : ι → ℝ) (T : Finset ι) :
    ∑ z : Cube ι, weight u z * chi T z = ∏ i ∈ T, u i := by sorry
