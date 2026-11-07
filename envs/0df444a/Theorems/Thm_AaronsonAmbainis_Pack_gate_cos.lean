-- Prove2me | Theorems.Thm_AaronsonAmbainis_Pack_gate_cos
-- name    : AaronsonAmbainis.Pack.gate_cos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:40:45.105703+00:00
-- url     : https://prove2.me/theorems/ab017386-47d3-4d59-90fd-a113b5aec1a0
-- title:
--   Pack: gate cos
-- statement:
--   The hypothesis `N (1 - cos (π / m)) ≤ 2` of the block inequality for `N = M ^ 2` and
--   `m = ⌈π M / 2⌉₊`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Pack/Gate.lean#L25-L53
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Pack/Gate.lean#L25-L53

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Pack_Gate
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Pack

theorem AaronsonAmbainis.Pack.gate_cos (M : ℕ) (hM : 0 < M) :
    ((M ^ 2 : ℕ) : ℝ) * (1 - Real.cos (Real.pi / ((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ))) ≤ 2 := by sorry
