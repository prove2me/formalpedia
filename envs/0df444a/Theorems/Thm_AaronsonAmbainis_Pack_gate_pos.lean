-- Prove2me | Theorems.Thm_AaronsonAmbainis_Pack_gate_pos
-- name    : AaronsonAmbainis.Pack.gate_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:40:30.596075+00:00
-- url     : https://prove2.me/theorems/c8d049aa-6c2d-4bec-85c3-fef1e174b5ef
-- title:
--   Pack: gate pos
-- statement:
--   `m = ⌈π M / 2⌉₊` is positive when `M` is.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Pack/Gate.lean#L18-L21
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Pack/Gate.lean#L18-L21

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Pack_Gate
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Pack

theorem AaronsonAmbainis.Pack.gate_pos (M : ℕ) (hM : 0 < M) : 0 < ⌈Real.pi * (M : ℝ) / 2⌉₊ := by sorry
