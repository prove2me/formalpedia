-- Prove2me | Theorems.Thm_FFactor_F2
-- name    : FFactor.F2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:57:02.486363+00:00
-- url     : https://prove2.me/theorems/5f73be7e-8757-458d-bd36-835d1f1c89f6
-- title:
--   FFactor: F2
-- statement:
--   The FFactor construction uses the F2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L127-L129
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L127-L129

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

theorem FFactor.F2 (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {v : V} (hv : v ∈ Tset G f U)
    {d : G.Dart} (hd : d.fst = v) : (.inl d : GV G f) ∉ U := by sorry
