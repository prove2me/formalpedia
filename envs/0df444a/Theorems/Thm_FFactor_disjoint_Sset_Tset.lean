-- Prove2me | Theorems.Thm_FFactor_disjoint_Sset_Tset
-- name    : FFactor.disjoint_Sset_Tset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:59:19.34481+00:00
-- url     : https://prove2.me/theorems/4bf62906-0f1a-4757-bcf6-4c5044e6e259
-- title:
--   FFactor: disjoint Sset Tset
-- statement:
--   The FFactor construction uses the disjoint Sset Tset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L109-L113
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L109-L113

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

theorem FFactor.disjoint_Sset_Tset : Disjoint (Sset G f U) (Tset G f U) := by sorry
