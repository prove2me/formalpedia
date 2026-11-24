-- Prove2me | Theorems.Thm_FFactor_lab_eq_of_adj_inl_inr
-- name    : FFactor.lab_eq_of_adj_inl_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T06:00:22.545806+00:00
-- url     : https://prove2.me/theorems/e2bffd40-dd06-4cb5-803f-db5aecf3ccbd
-- title:
--   FFactor: lab eq of adj inl inr
-- statement:
--   The FFactor construction uses the lab eq of adj inl inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L219-L229
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L219-L229

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

theorem FFactor.lab_eq_of_adj_inl_inr {d : G.Dart} {p : Σ v : V, Fin (G.degree v - f v)}
    (ha : (.inl d : GV G f) ∉ U) (hb : (.inr p : GV G f) ∉ U) (hadj : d.fst = p.1) :
    lab G f U (.inl d) = lab G f U (.inr p) := by sorry
