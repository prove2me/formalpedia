-- Prove2me | Theorems.Thm_FFactor_card_adj_split
-- name    : FFactor.card_adj_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T06:02:37.718366+00:00
-- url     : https://prove2.me/theorems/8425146a-d0d0-47f1-b9cf-aba4c15efc0f
-- title:
--   FFactor: card adj split
-- statement:
--   The FFactor construction uses the card adj split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L350-L353
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L350-L353

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

theorem FFactor.card_adj_split (t : V) (S : Finset V) :
    #{u | G.Adj t u ∧ u ∈ S} + #{u | G.Adj t u ∧ u ∉ S} = G.degree t := by sorry
