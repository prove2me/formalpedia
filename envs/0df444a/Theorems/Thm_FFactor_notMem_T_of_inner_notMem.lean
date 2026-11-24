-- Prove2me | Theorems.Thm_FFactor_notMem_T_of_inner_notMem
-- name    : FFactor.notMem_T_of_inner_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:58:29.367955+00:00
-- url     : https://prove2.me/theorems/f9642e79-9f19-4421-b89a-f74b47ab5cd3
-- title:
--   FFactor: not Mem T of inner not Mem
-- statement:
--   The FFactor construction uses the not Mem T of inner not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L216-L217
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L216-L217

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

theorem FFactor.notMem_T_of_inner_notMem {v : V} {i : Fin (G.degree v - f v)}
    (h : (.inr ⟨v, i⟩ : GV G f) ∉ U) : v ∉ Tset G f U := by sorry
