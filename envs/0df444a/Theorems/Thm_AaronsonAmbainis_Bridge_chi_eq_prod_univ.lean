-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_chi_eq_prod_univ
-- name    : AaronsonAmbainis.Bridge.chi_eq_prod_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:58:25.864658+00:00
-- url     : https://prove2.me/theorems/2effe866-e79b-4fbf-8093-a451a7a64a9e
-- title:
--   Bridge: chi eq prod univ
-- statement:
--   The Bridge construction uses the chi eq prod univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L36-L38
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L36-L38

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.chi_eq_prod_univ (S : Finset ι) (x : Cube ι) :
    chi S x = ∏ i, (if i ∈ S then sg (x i) else 1) := by sorry
