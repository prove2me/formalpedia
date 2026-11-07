-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_sg_mul_of_ne
-- name    : AaronsonAmbainis.Bridge.sg_mul_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:58:11.298686+00:00
-- url     : https://prove2.me/theorems/65a95329-6529-42ec-bf0c-921f7089b4ba
-- title:
--   Bridge: sg mul of ne
-- statement:
--   The Bridge construction uses the sg mul of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L28-L29
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L28-L29

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset

theorem AaronsonAmbainis.Bridge.sg_mul_of_ne {a b : Bool} (h : a ≠ b) : sg a * sg b = -1 := by sorry
