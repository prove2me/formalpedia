-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_two_pow_eq
-- name    : AaronsonAmbainis.Bridge.two_pow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:07:20.93319+00:00
-- url     : https://prove2.me/theorems/6709e332-f587-40e8-9015-c7bf1fa5619e
-- title:
--   Bridge: two pow eq
-- statement:
--   The Bridge construction uses the two pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L157-L160
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L157-L160

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.two_pow_eq {n : ℕ} (hn : 1 ≤ n) : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by sorry
