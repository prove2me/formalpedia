-- Prove2me | Theorems.Thm_FFactor_F5
-- name    : FFactor.F5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:57:20.090422+00:00
-- url     : https://prove2.me/theorems/7b795e6f-76d9-4da5-8f11-afc704636f79
-- title:
--   FFactor: F5
-- statement:
--   The FFactor construction uses the F5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L143-L145
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L143-L145

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

theorem FFactor.F5 {v : V} (hv : v ∈ Tset G f U) (i : Fin (G.degree v - f v)) :
    (.inr ⟨v, i⟩ : GV G f) ∈ U := by sorry
