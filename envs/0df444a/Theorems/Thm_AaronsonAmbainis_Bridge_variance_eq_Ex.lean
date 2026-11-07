-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_variance_eq_Ex
-- name    : AaronsonAmbainis.Bridge.variance_eq_Ex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:11:57.670376+00:00
-- url     : https://prove2.me/theorems/11a98542-9e9d-45c1-9750-b6400f4badfc
-- title:
--   Bridge: variance eq Ex
-- statement:
--   The Bridge construction uses the variance eq Ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L89-L93
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L89-L93

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.variance_eq_Ex {N : ℕ} (F : Cube (Fin N) → ℝ) :
    variance F = Ex (fun X => (F X - Ex F) ^ 2) := by sorry
