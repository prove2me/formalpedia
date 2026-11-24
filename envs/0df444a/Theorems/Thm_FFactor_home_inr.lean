-- Prove2me | Theorems.Thm_FFactor_home_inr
-- name    : FFactor.home_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:55:38.66724+00:00
-- url     : https://prove2.me/theorems/4451a5da-3329-4692-a79b-aafd8579561b
-- title:
--   FFactor: home inr
-- statement:
--   The FFactor construction uses the home inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L174-L175
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L174-L175

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
variable [DecidableEq V] {U : Set (GV G f)}

theorem FFactor.home_inr (p : Σ v : V, Fin (G.degree v - f v)) :
    home G f U (.inr p) = p.1 := by sorry

attribute [defeq] FFactor.home_inr
