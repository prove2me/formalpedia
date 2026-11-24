-- Prove2me | Theorems.Thm_FFactor_gadget_adj_inl_inl
-- name    : FFactor.gadget_adj_inl_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:51:49.376277+00:00
-- url     : https://prove2.me/theorems/5f767e57-0dfa-4998-925f-feb17dfad9fb
-- title:
--   FFactor: gadget adj inl inl
-- statement:
--   The FFactor construction uses the gadget adj inl inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorGadget.lean#L50-L51
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorGadget.lean#L50-L51

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorGadget
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] (G : SimpleGraph V) (f : V → ℕ)

theorem FFactor.gadget_adj_inl_inl {d d' : G.Dart} :
    (gadget G f).Adj (.inl d) (.inl d') ↔ d' = d.symm := by sorry
