-- Prove2me | Theorems.Thm_FFactor_lab_of_notMem
-- name    : FFactor.lab_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:55:33.728114+00:00
-- url     : https://prove2.me/theorems/f3095079-0547-4488-99a4-eb5b2c8b006d
-- title:
--   FFactor: lab of not Mem
-- statement:
--   The FFactor construction uses the lab of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L192-L194
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L192-L194

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

theorem FFactor.lab_of_notMem {a : GV G f} (h : home G f U a ∉ Sset G f U ∪ Tset G f U) :
    lab G f U a = .inl ((Gr G f U).connectedComponentMk ⟨home G f U a, h⟩) := by sorry
