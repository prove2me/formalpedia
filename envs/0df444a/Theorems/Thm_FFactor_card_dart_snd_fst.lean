-- Prove2me | Theorems.Thm_FFactor_card_dart_snd_fst
-- name    : FFactor.card_dart_snd_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T06:01:50.393875+00:00
-- url     : https://prove2.me/theorems/58ee8173-4384-400f-b44a-c548b9dcdfe1
-- title:
--   FFactor: card dart snd fst
-- statement:
--   The FFactor construction uses the card dart snd fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L65-L76
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L65-L76

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

theorem FFactor.card_dart_snd_fst (r : V) (T : Finset V) :
    #{d : G.Dart | d.fst ∈ T ∧ d.snd = r} = #{t ∈ T | G.Adj r t} := by sorry
