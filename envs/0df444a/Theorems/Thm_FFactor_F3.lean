-- Prove2me | Theorems.Thm_FFactor_F3
-- name    : FFactor.F3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:55:48.544462+00:00
-- url     : https://prove2.me/theorems/c2055825-4cfd-4f5a-907e-ebd417171d91
-- title:
--   FFactor: F3
-- statement:
--   The FFactor construction uses the F3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L131-L137
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L131-L137

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

theorem FFactor.F3 (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {v : V} (hvT : v ∉ Tset G f U)
    (hvS : v ∉ Sset G f U) {d : G.Dart} (hd : d.fst = v) : (.inl d : GV G f) ∉ U := by sorry
