-- Prove2me | Theorems.Thm_FFactor_outer_notMem_of_outer_notMem
-- name    : FFactor.outer_notMem_of_outer_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:59:15.725806+00:00
-- url     : https://prove2.me/theorems/913e3958-9a77-41ed-8276-512c842f94d3
-- title:
--   FFactor: outer not Mem of outer not Mem
-- statement:
--   The FFactor construction uses the outer not Mem of outer not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L65-L97
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L65-L97

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

theorem FFactor.outer_notMem_of_outer_notMem (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {v : V}
    (hT : ∀ i, (.inr ⟨v, i⟩ : GV G f) ∉ U) {z : G.Dart} (hz : z.fst = v)
    (hzU : (.inl z : GV G f) ∉ U) {d : G.Dart} (hd : d.fst = v) :
    (.inl d : GV G f) ∉ U := by sorry
