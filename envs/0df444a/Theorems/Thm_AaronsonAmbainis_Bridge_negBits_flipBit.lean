-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_negBits_flipBit
-- name    : AaronsonAmbainis.Bridge.negBits_flipBit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:46.635398+00:00
-- url     : https://prove2.me/theorems/cbede9e9-c252-4011-b6d8-f5f108d2d331
-- title:
--   Bridge: neg Bits flip Bit
-- statement:
--   The Bridge construction uses the neg Bits flip Bit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L404-L410
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L404-L410

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.negBits_flipBit {N : ℕ} (X : Fin N → Bool) (i : Fin N) :
    negBits (flipBit X i) = flipBit (negBits X) i := by sorry
