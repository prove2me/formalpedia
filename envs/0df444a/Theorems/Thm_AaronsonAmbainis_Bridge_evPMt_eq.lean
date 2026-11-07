-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_evPMt_eq
-- name    : AaronsonAmbainis.Bridge.evPMt_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:12:58.335478+00:00
-- url     : https://prove2.me/theorems/2215f7db-70e9-4c78-88dd-0581f4d5454c
-- title:
--   Bridge: ev PMt eq
-- statement:
--   The Bridge construction uses the ev PMt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L412-L419
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L412-L419

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.evPMt_eq {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (X : Fin N → Bool) :
    evPMt p X = evPM p (negBits X) := by sorry
