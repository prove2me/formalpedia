-- Prove2me | Theorems.Thm_FFactor_not_isTutteViolator_iff_le
-- name    : FFactor.not_isTutteViolator_iff_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T06:02:49.495021+00:00
-- url     : https://prove2.me/theorems/07ff6d94-1712-4249-9bd0-e5b1614cab8d
-- title:
--   FFactor: not is Tutte Violator iff le
-- statement:
--   The FFactor construction uses the not is Tutte Violator iff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L372-L374
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L372-L374

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorSuff
public import Definitions.Def_FFactorLib_FFactorCount
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : V → ℕ}
  {U : Set (GV G f)}
omit [DecidableEq V]

theorem FFactor.not_isTutteViolator_iff_le {U' : Set (GV G f)} :
    (gadget G f).IsTutteViolator U' ↔ U'.ncard < (del (gadget G f) U').oddComponents.ncard := by sorry
