-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_Ex_evPMt
-- name    : AaronsonAmbainis.Bridge.Ex_evPMt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:46.354042+00:00
-- url     : https://prove2.me/theorems/dd338307-9725-400a-99a4-6c3c92f6f548
-- title:
--   Bridge: Ex ev PMt
-- statement:
--   The Bridge construction uses the Ex ev PMt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L431-L434
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L431-L434

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.Ex_evPMt {N : ℕ} (p : MvPolynomial (Fin N) ℝ) : Ex (evPMt p) = Ex (evPM p) := by sorry
