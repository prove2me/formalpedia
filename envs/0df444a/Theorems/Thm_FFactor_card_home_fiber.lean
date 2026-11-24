-- Prove2me | Theorems.Thm_FFactor_card_home_fiber
-- name    : FFactor.card_home_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T06:02:00.284887+00:00
-- url     : https://prove2.me/theorems/049f74b9-86f1-4140-8c05-ff668a3a795c
-- title:
--   FFactor: card home fiber
-- statement:
--   The FFactor construction uses the card home fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L78-L108
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L78-L108

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

theorem FFactor.card_home_fiber {r : V} (hr : r ∉ Tset G f U) :
    #{a : GV G f | home G f U a = r} =
      G.degree r + #{t ∈ Tset G f U | G.Adj r t} + (G.degree r - f r) := by sorry
