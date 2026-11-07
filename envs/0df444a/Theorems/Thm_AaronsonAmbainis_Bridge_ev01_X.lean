-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_ev01_X
-- name    : AaronsonAmbainis.Bridge.ev01_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:18:33.35544+00:00
-- url     : https://prove2.me/theorems/8f6a24f7-0529-468b-8901-c8775c9925f5
-- title:
--   Bridge: ev01 X
-- statement:
--   The Bridge construction uses the ev01 X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Instance.lean#L23-L25
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Instance.lean#L23-L25

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Bridge_Instance
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.ev01_X {N : ℕ} (i : Fin N) (Y : Fin N → Bool) :
    ev01 (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) Y = if Y i then 1 else 0 := by sorry
