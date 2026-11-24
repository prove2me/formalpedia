-- Prove2me | Theorems.Thm_FFactor_lab_eq_of_adj
-- name    : FFactor.lab_eq_of_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T06:00:14.055098+00:00
-- url     : https://prove2.me/theorems/00c952a7-08d1-4ac1-955f-3a37c1a7a06d
-- title:
--   FFactor: lab eq of adj
-- statement:
--   The FFactor construction uses the lab eq of adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L231-L253
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L231-L253

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
variable [DecidableEq V] {U : Set (GV G f)}

theorem FFactor.lab_eq_of_adj (a b : GV G f) (ha : a ∉ U) (hb : b ∉ U) (hadj : (gadget G f).Adj a b) :
    lab G f U a = lab G f U b := by sorry
