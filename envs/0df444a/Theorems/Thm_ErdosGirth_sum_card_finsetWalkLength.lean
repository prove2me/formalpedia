-- Prove2me | Theorems.Thm_ErdosGirth_sum_card_finsetWalkLength
-- name    : ErdosGirth.sum_card_finsetWalkLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:00.920257+00:00
-- url     : https://prove2.me/theorems/ffbcc1aa-6e4b-4261-bf96-5328ef32b85d
-- title:
--   Erdos Girth: sum card finset Walk Length
-- statement:
--   The Erdos Girth construction uses the sum card finset Walk Length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L77-L97
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L77-L97

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth

theorem ErdosGirth.sum_card_finsetWalkLength {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) (u : V) :
    ∑ v, #(G.finsetWalkLength n u v) ≤ Fintype.card V ^ n := by sorry
