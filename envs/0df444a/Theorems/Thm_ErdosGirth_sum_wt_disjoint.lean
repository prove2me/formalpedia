-- Prove2me | Theorems.Thm_ErdosGirth_sum_wt_disjoint
-- name    : ErdosGirth.sum_wt_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:27:50.308058+00:00
-- url     : https://prove2.me/theorems/f01aa0b2-a404-5cba-af27-85712fcc5fb4
-- title:
--   Erdos Girth: sum wt disjoint
-- statement:
--   The Erdos Girth construction uses the sum wt disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L59-L76
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L59-L76

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth

theorem ErdosGirth.sum_wt_disjoint {m : ℕ} (p : ℝ) {B : Finset (Sym2 (Fin m))} (hB : B ⊆ pairs m) :
    ∑ S ∈ (pairs m).powerset, (if Disjoint B S then wt m p S else 0) = (1 - p) ^ B.card := by sorry
