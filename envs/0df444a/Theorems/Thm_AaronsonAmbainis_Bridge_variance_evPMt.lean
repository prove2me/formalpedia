-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_variance_evPMt
-- name    : AaronsonAmbainis.Bridge.variance_evPMt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:14:37.770237+00:00
-- url     : https://prove2.me/theorems/815abb0e-790b-48b5-9a3e-ce4ed9d30d73
-- title:
--   Bridge: variance ev PMt
-- statement:
--   The Bridge construction uses the variance ev PMt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L436-L440
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L436-L440

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.variance_evPMt {N : ℕ} (p : MvPolynomial (Fin N) ℝ) :
    Ex (fun X => (evPMt p X - Ex (evPMt p)) ^ 2) = Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) := by sorry
