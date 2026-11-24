-- Prove2me | Theorems.Thm_FFactor_even_sum_card_adj
-- name    : FFactor.even_sum_card_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:53:23.171798+00:00
-- url     : https://prove2.me/theorems/be48bd5d-89b8-48c0-84b6-6fae2c4850a4
-- title:
--   FFactor: even sum card adj
-- statement:
--   Handshake lemma inside a finset.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorNec.lean#L28-L49
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorNec.lean#L28-L49

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorNec
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem FFactor.even_sum_card_adj (H : SimpleGraph V) [DecidableRel H.Adj] (s : Finset V) :
    Even (∑ w ∈ s, #{u ∈ s | H.Adj w u}) := by sorry
