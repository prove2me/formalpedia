-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_chi_eq_prod_sg
-- name    : AaronsonAmbainis.Bridge.chi_eq_prod_sg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:56:53.859897+00:00
-- url     : https://prove2.me/theorems/acc78e7d-f1c0-4beb-9806-926c3a3935d3
-- title:
--   Bridge: chi eq prod sg
-- statement:
--   The Bridge construction uses the chi eq prod sg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L31-L32
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L31-L32

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset

theorem AaronsonAmbainis.Bridge.chi_eq_prod_sg {ι : Type*} (S : Finset ι) (x : Cube ι) : chi S x = ∏ i ∈ S, sg (x i) := by sorry
