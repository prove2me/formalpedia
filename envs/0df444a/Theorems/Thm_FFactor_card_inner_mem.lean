-- Prove2me | Theorems.Thm_FFactor_card_inner_mem
-- name    : FFactor.card_inner_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:58:52.86311+00:00
-- url     : https://prove2.me/theorems/17c1f4f8-c940-42ec-9167-daa6c5a34359
-- title:
--   FFactor: card inner mem
-- statement:
--   The FFactor construction uses the card inner mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L313-L325
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L313-L325

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

theorem FFactor.card_inner_mem (s0 : Finset V) :
    #{p : Σ v : V, Fin (G.degree v - f v) | p.1 ∈ s0} = ∑ v ∈ s0, (G.degree v - f v) := by sorry
