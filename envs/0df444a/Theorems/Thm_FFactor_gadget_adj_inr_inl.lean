-- Prove2me | Theorems.Thm_FFactor_gadget_adj_inr_inl
-- name    : FFactor.gadget_adj_inr_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:51:39.98679+00:00
-- url     : https://prove2.me/theorems/aa65cfe9-78f9-4bab-976b-7b5608f7b73c
-- title:
--   FFactor: gadget adj inr inl
-- statement:
--   The FFactor construction uses the gadget adj inr inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorGadget.lean#L54-L55
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorGadget.lean#L54-L55

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorGadget
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] (G : SimpleGraph V) (f : V → ℕ)

theorem FFactor.gadget_adj_inr_inl {d : G.Dart} {p : Σ v : V, Fin (G.degree v - f v)} :
    (gadget G f).Adj (.inr p) (.inl d) ↔ d.fst = p.1 := by sorry
