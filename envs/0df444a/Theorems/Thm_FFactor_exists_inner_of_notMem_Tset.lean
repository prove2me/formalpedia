-- Prove2me | Theorems.Thm_FFactor_exists_inner_of_notMem_Tset
-- name    : FFactor.exists_inner_of_notMem_Tset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:56:13.146984+00:00
-- url     : https://prove2.me/theorems/4bc33361-fc7a-4598-8537-33fac1227fa4
-- title:
--   FFactor: exists inner of not Mem Tset
-- statement:
--   The FFactor construction uses the exists inner of not Mem Tset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L147-L151
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L147-L151

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

theorem FFactor.exists_inner_of_notMem_Tset {v : V} (hv : v ∉ Tset G f U) :
    ∃ _ : Fin (G.degree v - f v), True := by sorry
