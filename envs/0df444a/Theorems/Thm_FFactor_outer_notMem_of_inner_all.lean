-- Prove2me | Theorems.Thm_FFactor_outer_notMem_of_inner_all
-- name    : FFactor.outer_notMem_of_inner_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:59:00.941826+00:00
-- url     : https://prove2.me/theorems/4fa76554-e875-480e-8d21-689a048727cf
-- title:
--   FFactor: outer not Mem of inner all
-- statement:
--   The FFactor construction uses the outer not Mem of inner all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L48-L63
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L48-L63

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
variable {U : Set (GV G f)}

theorem FFactor.outer_notMem_of_inner_all (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {v : V}
    (hT : ∀ i, (.inr ⟨v, i⟩ : GV G f) ∈ U) {d : G.Dart} (hd : d.fst = v) :
    (.inl d : GV G f) ∉ U := by sorry
