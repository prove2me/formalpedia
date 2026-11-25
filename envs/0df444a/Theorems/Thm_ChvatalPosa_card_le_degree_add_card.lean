-- Prove2me | Theorems.Thm_ChvatalPosa_card_le_degree_add_card
-- name    : ChvatalPosa.card_le_degree_add_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:18:29.696667+00:00
-- url     : https://prove2.me/theorems/acc40f90-6e8d-57b3-b2a7-895cd1e631fa
-- title:
--   Chvatal Posa: card le degree add card
-- statement:
--   If `S` contains every non-neighbour of `v` (including `v`), then `n ≤ deg v + #S`.
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/ChvatalPosaLib/ChvatalPosa.lean#L54-L62
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/ChvatalPosaLib/ChvatalPosa.lean#L54-L62

module
public import Mathlib
public import Definitions.Def_MengerHamilton_Hamiltonian
public import Definitions.Def_ChvatalPosaLib_ChvatalPosa
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ChvatalPosa
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
omit [DecidableEq V]

theorem ChvatalPosa.card_le_degree_add_card (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) (S : Finset V)
    (hS : ∀ w, ¬ H.Adj v w → w ∈ S) : Fintype.card V ≤ H.degree v + #S := by sorry
