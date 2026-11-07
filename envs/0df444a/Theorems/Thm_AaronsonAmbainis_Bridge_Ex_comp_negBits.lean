-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_Ex_comp_negBits
-- name    : AaronsonAmbainis.Bridge.Ex_comp_negBits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:12:44.332497+00:00
-- url     : https://prove2.me/theorems/cd9e1777-c3a6-46cc-993c-6d705d4f2168
-- title:
--   Bridge: Ex comp neg Bits
-- statement:
--   The Bridge construction uses the Ex comp neg Bits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L398-L402
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L398-L402

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.Ex_comp_negBits {N : ℕ} (F : (Fin N → Bool) → ℝ) :
    Ex (fun X => F (negBits X)) = Ex F := by sorry
