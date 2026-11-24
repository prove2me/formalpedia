-- Prove2me | Theorems.Thm_FFactor_card_dart_fst_mem
-- name    : FFactor.card_dart_fst_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T06:02:09.867679+00:00
-- url     : https://prove2.me/theorems/f7212eb4-ba2b-42ad-bf6f-32801b1a3389
-- title:
--   FFactor: card dart fst mem
-- statement:
--   The FFactor construction uses the card dart fst mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L300-L311
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L300-L311

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorSuff
public import Definitions.Def_FFactorLib_FFactorCount
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : V → ℕ}
  {U : Set (GV G f)}

theorem FFactor.card_dart_fst_mem (s0 : Finset V) :
    #{d : G.Dart | d.fst ∈ s0} = ∑ v ∈ s0, G.degree v := by sorry
