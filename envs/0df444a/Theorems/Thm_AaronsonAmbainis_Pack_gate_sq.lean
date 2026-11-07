-- Prove2me | Theorems.Thm_AaronsonAmbainis_Pack_gate_sq
-- name    : AaronsonAmbainis.Pack.gate_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:40:52.262479+00:00
-- url     : https://prove2.me/theorems/23e6a6be-7120-450e-8e62-27dc3259a9b1
-- title:
--   Pack: gate sq
-- statement:
--   `4 m² ≤ (π M + 2)²` for `m = ⌈π M / 2⌉₊`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Pack/Gate.lean#L56-L71
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Pack/Gate.lean#L56-L71

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Pack_Gate
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Pack

theorem AaronsonAmbainis.Pack.gate_sq (M : ℕ) :
    4 * (((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ)) ^ 2 ≤ (Real.pi * (M : ℝ) + 2) ^ 2 := by sorry
