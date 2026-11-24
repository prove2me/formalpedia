-- Prove2me | Theorems.Thm_FFactor_exists_min_violator
-- name    : FFactor.exists_min_violator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:51:32.702294+00:00
-- url     : https://prove2.me/theorems/21dced11-0f8d-41ad-a22d-00d8fa5a5403
-- title:
--   FFactor: exists min violator
-- statement:
--   There is a Tutte violator none of whose vertices satisfies `TwoComp`.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorComp.lean#L224-L239
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorComp.lean#L224-L239

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {W : Type*} (Γ : SimpleGraph W)

theorem FFactor.exists_min_violator [Finite W] (h : ∃ U, Γ.IsTutteViolator U) :
    ∃ U, Γ.IsTutteViolator U ∧ ∀ x ∈ U, ¬ TwoComp Γ U x := by sorry
