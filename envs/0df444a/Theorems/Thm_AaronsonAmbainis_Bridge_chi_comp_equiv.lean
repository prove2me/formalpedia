-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_chi_comp_equiv
-- name    : AaronsonAmbainis.Bridge.chi_comp_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:49:18.490388+00:00
-- url     : https://prove2.me/theorems/faf165bd-0695-4ef1-a569-29bcb2f89db6
-- title:
--   Bridge: chi comp equiv
-- statement:
--   The Bridge construction uses the chi comp equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Transport.lean#L26-L28
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Transport.lean#L26-L28

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem AaronsonAmbainis.Bridge.chi_comp_equiv (e : ι ≃ κ) (S : Finset ι) (y : Cube κ) :
    chi S (fun i => y (e i)) = chi (S.map e.toEmbedding) y := by sorry
