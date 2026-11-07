-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_mean_eq_Ex
-- name    : AaronsonAmbainis.Bridge.mean_eq_Ex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:15.261936+00:00
-- url     : https://prove2.me/theorems/a4d092b0-f284-471c-a053-6fa9a8bfcb84
-- title:
--   Bridge: mean eq Ex
-- statement:
--   The Bridge construction uses the mean eq Ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L75-L77
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L75-L77

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.mean_eq_Ex {N : ℕ} (F : Cube (Fin N) → ℝ) : mean F = Ex F := by sorry
