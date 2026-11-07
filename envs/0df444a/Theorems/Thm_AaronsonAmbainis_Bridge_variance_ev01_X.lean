-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_variance_ev01_X
-- name    : AaronsonAmbainis.Bridge.variance_ev01_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:20:05.70191+00:00
-- url     : https://prove2.me/theorems/2632c723-09c8-47c2-bcae-944c0dc615cb
-- title:
--   Bridge: variance ev01 X
-- statement:
--   The Bridge construction uses the variance ev01 X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Instance.lean#L72-L75
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Instance.lean#L72-L75

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Bridge_Instance
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.variance_ev01_X {N : ℕ} (i : Fin N) :
    variance (ev01 (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) : Cube (Fin N) → ℝ) = 1 / 4 := by sorry
