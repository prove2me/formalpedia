-- Prove2me | Theorems.Thm_FFactor_F4
-- name    : FFactor.F4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:57:39.062983+00:00
-- url     : https://prove2.me/theorems/2e89ac82-c4f0-46fd-8331-1d5c26ee4af3
-- title:
--   FFactor: F4
-- statement:
--   The FFactor construction uses the F4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L139-L141
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L139-L141

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

theorem FFactor.F4 {v : V} (hv : v ∈ Sset G f U) {d : G.Dart} (hd : d.fst = v) :
    (.inl d : GV G f) ∈ U := by sorry
