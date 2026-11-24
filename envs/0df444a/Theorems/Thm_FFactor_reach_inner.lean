-- Prove2me | Theorems.Thm_FFactor_reach_inner
-- name    : FFactor.reach_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:56:22.186988+00:00
-- url     : https://prove2.me/theorems/af1dc66d-55f1-4626-bc7e-0c02b04b33cf
-- title:
--   FFactor: reach inner
-- statement:
--   The FFactor construction uses the reach inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L267-L286
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L267-L286

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

theorem FFactor.reach_inner (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {r : V}
    (hr : r ∉ Sset G f U ∪ Tset G f U) (x : GV G f) (hx : x ∉ U)
    (hxr : home G f U x = r) (i : Fin (G.degree r - f r)) :
    (del (gadget G f) U).Reachable ⟨x, (mem_del_verts _).mpr hx⟩
      ⟨.inr ⟨r, i⟩, (mem_del_verts _).mpr (F1 hmin (notMem_T_of_notMem_union hr) i)⟩ := by sorry
