-- Prove2me | Theorems.Thm_FFactor_lab_eq_of_home_eq
-- name    : FFactor.lab_eq_of_home_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:57:50.537041+00:00
-- url     : https://prove2.me/theorems/9cae5db0-059f-4150-b9b3-16705c359361
-- title:
--   FFactor: lab eq of home eq
-- statement:
--   The FFactor construction uses the lab eq of home eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L205-L209
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L205-L209

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

theorem FFactor.lab_eq_of_home_eq {a b : GV G f} (hab : home G f U a = home G f U b)
    (h : home G f U a ∉ Sset G f U ∪ Tset G f U) : lab G f U a = lab G f U b := by sorry
