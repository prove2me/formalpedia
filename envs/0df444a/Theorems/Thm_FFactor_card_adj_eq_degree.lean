-- Prove2me | Theorems.Thm_FFactor_card_adj_eq_degree
-- name    : FFactor.card_adj_eq_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T06:02:42.705945+00:00
-- url     : https://prove2.me/theorems/bd212ca4-701a-4b9b-92c5-e0a98b9822b0
-- title:
--   FFactor: card adj eq degree
-- statement:
--   The FFactor construction uses the card adj eq degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L344-L348
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L344-L348

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
omit [DecidableEq V]

theorem FFactor.card_adj_eq_degree (v : V) : #{u | G.Adj v u} = G.degree v := by sorry
