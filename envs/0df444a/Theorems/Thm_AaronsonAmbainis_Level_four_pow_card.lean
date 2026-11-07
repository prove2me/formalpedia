-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_four_pow_card
-- name    : AaronsonAmbainis.Level.four_pow_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:34:59.757859+00:00
-- url     : https://prove2.me/theorems/c5ebbd42-6ba0-4fdf-95bb-509133544bd0
-- title:
--   Level: four pow card
-- statement:
--   `4 ^ n = 4 · 4 ^ (n - 1)` for `n ≥ 1`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L48-L53
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Basic.lean#L48-L53

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.Level.four_pow_card [Nonempty ι] :
    (4 : ℝ) ^ Fintype.card ι = 4 * 4 ^ (Fintype.card ι - 1) := by sorry
