-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_evPM_X_eq_dict
-- name    : AaronsonAmbainis.Bridge.evPM_X_eq_dict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:19:00.748888+00:00
-- url     : https://prove2.me/theorems/10bcc725-dad9-42e7-a7b2-e739fbb17ab7
-- title:
--   Bridge: ev PM X eq dict
-- statement:
--   The Bridge construction uses the ev PM X eq dict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Instance.lean#L66-L70
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Instance.lean#L66-L70

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Bridge_Instance
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.evPM_X_eq_dict {N : ℕ} (i : Fin N) :
    (evPM (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) : Cube (Fin N) → ℝ) = dict i := by sorry
