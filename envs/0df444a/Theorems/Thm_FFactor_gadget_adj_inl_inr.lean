-- Prove2me | Theorems.Thm_FFactor_gadget_adj_inl_inr
-- name    : FFactor.gadget_adj_inl_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:51:49.071806+00:00
-- url     : https://prove2.me/theorems/bb5904e7-0a4e-4be2-8636-152e67e4171d
-- title:
--   FFactor: gadget adj inl inr
-- statement:
--   The FFactor construction uses the gadget adj inl inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorGadget.lean#L52-L53
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorGadget.lean#L52-L53

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorGadget
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] (G : SimpleGraph V) (f : V → ℕ)

theorem FFactor.gadget_adj_inl_inr {d : G.Dart} {p : Σ v : V, Fin (G.degree v - f v)} :
    (gadget G f).Adj (.inl d) (.inr p) ↔ d.fst = p.1 := by sorry
