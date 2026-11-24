-- Prove2me | Theorems.Thm_FFactor_fst_notMem_S_of_notMem
-- name    : FFactor.fst_notMem_S_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:56:30.111918+00:00
-- url     : https://prove2.me/theorems/9fda1276-202d-409d-b4f5-e25c45e86929
-- title:
--   FFactor: fst not Mem S of not Mem
-- statement:
--   The FFactor construction uses the fst not Mem S of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L212-L213
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L212-L213

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
omit [DecidableEq V]

theorem FFactor.fst_notMem_S_of_notMem {d : G.Dart} (hd : (.inl d : GV G f) ∉ U) :
    d.fst ∉ Sset G f U := by sorry
