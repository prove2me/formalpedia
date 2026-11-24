-- Prove2me | Theorems.Thm_FFactor_card_inner_fiber
-- name    : FFactor.card_inner_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:58:09.682131+00:00
-- url     : https://prove2.me/theorems/7157f281-5624-4539-a0bf-67965530163c
-- title:
--   FFactor: card inner fiber
-- statement:
--   The FFactor construction uses the card inner fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L51-L63
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L51-L63

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

theorem FFactor.card_inner_fiber (r : V) :
    #{p : Σ v : V, Fin (G.degree v - f v) | p.1 = r} = G.degree r - f r := by sorry
