-- Prove2me | Theorems.Thm_FFactor_lab_inl_of_mem
-- name    : FFactor.lab_inl_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:55:43.283814+00:00
-- url     : https://prove2.me/theorems/88a707fe-4fa7-4498-bae2-945e06b9524e
-- title:
--   FFactor: lab inl of mem
-- statement:
--   The FFactor construction uses the lab inl of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L196-L198
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L196-L198

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

theorem FFactor.lab_inl_of_mem {d : G.Dart} (h : home G f U (.inl d) ∈ Sset G f U ∪ Tset G f U) :
    lab G f U (.inl d) = .inr (.inl d.edge) := by sorry
