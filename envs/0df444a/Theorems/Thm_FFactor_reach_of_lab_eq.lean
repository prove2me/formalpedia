-- Prove2me | Theorems.Thm_FFactor_reach_of_lab_eq
-- name    : FFactor.reach_of_lab_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T06:01:14.601993+00:00
-- url     : https://prove2.me/theorems/a7e5f46b-9d19-4f99-ac73-afa26fff83c6
-- title:
--   FFactor: reach of lab eq
-- statement:
--   The FFactor construction uses the reach of lab eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L320-L363
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L320-L363

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

theorem FFactor.reach_of_lab_eq (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) (a b : GV G f)
    (ha : a ∉ U) (hb : b ∉ U) (hab : lab G f U a = lab G f U b) :
    (del (gadget G f) U).Reachable ⟨a, (mem_del_verts _).mpr ha⟩
      ⟨b, (mem_del_verts _).mpr hb⟩ := by sorry
