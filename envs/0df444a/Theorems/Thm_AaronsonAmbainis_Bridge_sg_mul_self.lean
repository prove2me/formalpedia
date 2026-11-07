-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_sg_mul_self
-- name    : AaronsonAmbainis.Bridge.sg_mul_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:56:58.741142+00:00
-- url     : https://prove2.me/theorems/63e35e03-8760-4f9d-ac8c-21002f576e2f
-- title:
--   Bridge: sg mul self
-- statement:
--   The Bridge construction uses the sg mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L22-L23
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L22-L23

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset

theorem AaronsonAmbainis.Bridge.sg_mul_self (b : Bool) : sg b * sg b = 1 := by sorry
