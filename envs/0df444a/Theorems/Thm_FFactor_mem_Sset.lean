-- Prove2me | Theorems.Thm_FFactor_mem_Sset
-- name    : FFactor.mem_Sset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:57:14.119275+00:00
-- url     : https://prove2.me/theorems/d8622215-51e0-4a8a-87e4-7504ee13833b
-- title:
--   FFactor: mem Sset
-- statement:
--   The FFactor construction uses the mem Sset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L118-L120
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L118-L120

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
variable {U : Set (GV G f)}

theorem FFactor.mem_Sset {v : V} : v ∈ Sset G f U ↔
    v ∉ Tset G f U ∧ ∀ d : G.Dart, d.fst = v → (.inl d : GV G f) ∈ U := by sorry
