-- Prove2me | Theorems.Thm_ErdosGirth_sum_card_closed_walks
-- name    : ErdosGirth.sum_card_closed_walks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:02.703432+00:00
-- url     : https://prove2.me/theorems/2d691bac-4d6d-40ff-a562-41ad0c3297d4
-- title:
--   Erdos Girth: sum card closed walks
-- statement:
--   The Erdos Girth construction uses the sum card closed walks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L99-L115
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L99-L115

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth

theorem ErdosGirth.sum_card_closed_walks {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) :
    ∑ u, #(G.finsetWalkLength (n + 1) u u) ≤ Fintype.card V ^ (n + 1) := by sorry
