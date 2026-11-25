-- Prove2me | Theorems.Thm_ErdosGirth_disjoint_of_isIndepSet
-- name    : ErdosGirth.disjoint_of_isIndepSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:28.253407+00:00
-- url     : https://prove2.me/theorems/714bd6f6-05af-5dc2-8fe1-5d5c23ce656a
-- title:
--   Erdos Girth: disjoint of is Indep Set
-- statement:
--   The Erdos Girth construction uses the disjoint of is Indep Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L224-L230
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L224-L230

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth

theorem ErdosGirth.disjoint_of_isIndepSet {m : ℕ} {S : Finset (Sym2 (Fin m))} {T : Finset (Fin m)}
    (h : (gr S).IsIndepSet (T : Set (Fin m))) : Disjoint (edgesIn T) S := by sorry
