-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_ev01_X_eq_affine
-- name    : AaronsonAmbainis.Bridge.ev01_X_eq_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:19:10.447656+00:00
-- url     : https://prove2.me/theorems/9709ee2b-ffbb-412d-9ffa-97857a395f7a
-- title:
--   Bridge: ev01 X eq affine
-- statement:
--   The Bridge construction uses the ev01 X eq affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Instance.lean#L58-L64
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Instance.lean#L58-L64

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Bridge_Instance
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.ev01_X_eq_affine {N : ℕ} (i : Fin N) :
    (ev01 (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) : Cube (Fin N) → ℝ)
      = fun Y => 1 / 2 + (-1 / 2) * dict i Y := by sorry
