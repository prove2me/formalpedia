-- Prove2me | Theorems.Thm_FFactor_delIncl_injective
-- name    : FFactor.delIncl_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:51:36.885651+00:00
-- url     : https://prove2.me/theorems/c1cf641b-74a3-46fd-8f5e-a9d5be09d4e7
-- title:
--   FFactor: del Incl injective
-- statement:
--   The FFactor construction uses the del Incl injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorComp.lean#L99-L102
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorComp.lean#L99-L102

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {W : Type*} (Γ : SimpleGraph W)

theorem FFactor.delIncl_injective (U : Set W) (x : W) : Function.Injective (delIncl Γ U x) := by sorry
