-- Prove2me | Theorems.Thm_FFactor_reach_adj
-- name    : FFactor.reach_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:56:32.443401+00:00
-- url     : https://prove2.me/theorems/42b21a28-b603-4c4c-9684-45e7dd7117f9
-- title:
--   FFactor: reach adj
-- statement:
--   The FFactor construction uses the reach adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L256-L259
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L256-L259

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
public import Theorems.Thm_FFactor_mem_del_verts
attribute [local simp] FFactor.mem_del_verts


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
variable [DecidableEq V] {U : Set (GV G f)}
omit [DecidableEq V]

theorem FFactor.reach_adj {a b : GV G f} (ha : a ∉ U) (hb : b ∉ U) (h : (gadget G f).Adj a b) :
    (del (gadget G f) U).Reachable ⟨a, (mem_del_verts _).mpr ha⟩
      ⟨b, (mem_del_verts _).mpr hb⟩ := by sorry
