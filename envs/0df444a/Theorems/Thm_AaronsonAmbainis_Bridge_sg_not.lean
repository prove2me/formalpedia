-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_sg_not
-- name    : AaronsonAmbainis.Bridge.sg_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:57:40.647196+00:00
-- url     : https://prove2.me/theorems/9b79da98-438e-40bc-a748-955c677c6e32
-- title:
--   Bridge: sg not
-- statement:
--   The Bridge construction uses the sg not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L25-L26
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L25-L26

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset

theorem AaronsonAmbainis.Bridge.sg_not (b : Bool) : sg (!b) = -sg b := by sorry
