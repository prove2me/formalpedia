-- Prove2me | Theorems.Thm_ErdosGirth_one_le_cyc
-- name    : ErdosGirth.one_le_cyc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:57.228851+00:00
-- url     : https://prove2.me/theorems/ff4ffe23-6049-4774-bf4d-aef103543fb0
-- title:
--   Erdos Girth: one le cyc
-- statement:
--   The Erdos Girth construction uses the one le cyc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L240-L270
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L240-L270

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
open Classical

theorem ErdosGirth.one_le_cyc {m g : ℕ} {S : Finset (Sym2 (Fin m))} {u : Fin m} (c : (gr S).Walk u u)
    (hc : c.IsCycle) (hl : c.length ≤ g) : 1 ≤ cyc m g S u := by sorry
