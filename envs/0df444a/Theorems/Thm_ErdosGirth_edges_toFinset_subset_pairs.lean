-- Prove2me | Theorems.Thm_ErdosGirth_edges_toFinset_subset_pairs
-- name    : ErdosGirth.edges_toFinset_subset_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:11.407421+00:00
-- url     : https://prove2.me/theorems/64c7bfce-5afd-4a3b-a0f7-f66795033741
-- title:
--   Erdos Girth: edges to Finset subset pairs
-- statement:
--   The Erdos Girth construction uses the edges to Finset subset pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L124-L129
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L124-L129

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth

theorem ErdosGirth.edges_toFinset_subset_pairs {m : ℕ} {u v : Fin m} (c : (⊤ : SimpleGraph (Fin m)).Walk u v) :
    c.edges.toFinset ⊆ pairs m := by sorry
