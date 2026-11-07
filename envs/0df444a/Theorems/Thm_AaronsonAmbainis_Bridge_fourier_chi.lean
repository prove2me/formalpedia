-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_fourier_chi
-- name    : AaronsonAmbainis.Bridge.fourier_chi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:59:39.803395+00:00
-- url     : https://prove2.me/theorems/e568b63e-4958-4f10-9e8a-07dbcc6bcd19
-- title:
--   Bridge: fourier chi
-- statement:
--   The Bridge construction uses the fourier chi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L169-L173
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L169-L173

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.fourier_chi (S T : Finset ι) : fourier (chi S) T = if S = T then 1 else 0 := by sorry
