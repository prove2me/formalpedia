-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_evPMt_bound_iff
-- name    : AaronsonAmbainis.Bridge.evPMt_bound_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:16:40.592149+00:00
-- url     : https://prove2.me/theorems/c79b4366-f84b-443b-9105-6f0a7c8893d8
-- title:
--   Bridge: ev PMt bound iff
-- statement:
--   The Bridge construction uses the ev PMt bound iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L421-L429
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L421-L429

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.evPMt_bound_iff {N : ℕ} (p : MvPolynomial (Fin N) ℝ) :
    (∀ X, |evPMt p X| ≤ 1) ↔ ∀ X, |evPM p X| ≤ 1 := by sorry
