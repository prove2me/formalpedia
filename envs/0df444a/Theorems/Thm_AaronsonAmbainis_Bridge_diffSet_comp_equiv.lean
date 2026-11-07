-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_diffSet_comp_equiv
-- name    : AaronsonAmbainis.Bridge.diffSet_comp_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:49:08.703203+00:00
-- url     : https://prove2.me/theorems/0d0320e5-40df-4d38-9e82-6cf5a2793435
-- title:
--   Bridge: diff Set comp equiv
-- statement:
--   The Bridge construction uses the diff Set comp equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Transport.lean#L47-L57
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Transport.lean#L47-L57

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [DecidableEq ι] [DecidableEq κ]

theorem AaronsonAmbainis.Bridge.diffSet_comp_equiv (e : ι ≃ κ) (x y : Cube ι) :
    diffSet (fun k => x (e.symm k)) (fun k => y (e.symm k))
      = (diffSet x y).map e.toEmbedding := by sorry
