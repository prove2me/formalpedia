-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_evPM_X
-- name    : AaronsonAmbainis.Bridge.evPM_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:18:30.771427+00:00
-- url     : https://prove2.me/theorems/2e91760e-2817-49f6-be38-39a3869d159e
-- title:
--   Bridge: ev PM X
-- statement:
--   The Bridge construction uses the ev PM X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Instance.lean#L27-L29
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Instance.lean#L27-L29

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Bridge_Instance
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.evPM_X {N : ℕ} (i : Fin N) (Y : Fin N → Bool) :
    evPM (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) Y = if Y i then -1 else 1 := by sorry
