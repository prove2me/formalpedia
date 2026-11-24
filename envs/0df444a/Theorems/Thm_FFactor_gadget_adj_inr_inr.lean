-- Prove2me | Theorems.Thm_FFactor_gadget_adj_inr_inr
-- name    : FFactor.gadget_adj_inr_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:51:54.6918+00:00
-- url     : https://prove2.me/theorems/990c9674-4c07-4baf-babc-1b92f5e10177
-- title:
--   FFactor: gadget adj inr inr
-- statement:
--   The FFactor construction uses the gadget adj inr inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorGadget.lean#L56-L57
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorGadget.lean#L56-L57

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorGadget
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] (G : SimpleGraph V) (f : V → ℕ)

theorem FFactor.gadget_adj_inr_inr {p q : Σ v : V, Fin (G.degree v - f v)} :
    ¬ (gadget G f).Adj (.inr p) (.inr q) := by sorry
