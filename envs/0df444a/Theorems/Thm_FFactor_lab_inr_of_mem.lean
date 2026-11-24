-- Prove2me | Theorems.Thm_FFactor_lab_inr_of_mem
-- name    : FFactor.lab_inr_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:55:51.091661+00:00
-- url     : https://prove2.me/theorems/51d0ca00-5b7d-4c16-9ee3-3bb45dcd2e54
-- title:
--   FFactor: lab inr of mem
-- statement:
--   The FFactor construction uses the lab inr of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L200-L203
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L200-L203

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

theorem FFactor.lab_inr_of_mem {p : Σ v : V, Fin (G.degree v - f v)}
    (h : home G f U (.inr p) ∈ Sset G f U ∪ Tset G f U) :
    lab G f U (.inr p) = .inr (.inr (.inr p)) := by sorry
