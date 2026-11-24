-- Prove2me | Theorems.Thm_FFactor_home_inl
-- name    : FFactor.home_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:56:00.508742+00:00
-- url     : https://prove2.me/theorems/4ceabb64-69c1-4ec1-8234-70af955b0340
-- title:
--   FFactor: home inl
-- statement:
--   The FFactor construction uses the home inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L172-L173
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L172-L173

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

theorem FFactor.home_inl (d : G.Dart) :
    home G f U (.inl d) = if d.fst ∈ Tset G f U then d.snd else d.fst := by sorry

attribute [defeq] FFactor.home_inl
