-- Prove2me | Theorems.Thm_FFactor_notMem_S_of_notMem_union
-- name    : FFactor.notMem_S_of_notMem_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:57:09.674823+00:00
-- url     : https://prove2.me/theorems/a62eb53c-c9fa-46f7-99ca-7d8cc4c6f746
-- title:
--   FFactor: not Mem S of not Mem union
-- statement:
--   The FFactor construction uses the not Mem S of not Mem union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L264-L265
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L264-L265

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

theorem FFactor.notMem_S_of_notMem_union {r : V} (hr : r ∉ Sset G f U ∪ Tset G f U) :
    r ∉ Sset G f U := by sorry
