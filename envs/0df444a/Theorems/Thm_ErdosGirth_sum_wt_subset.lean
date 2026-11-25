-- Prove2me | Theorems.Thm_ErdosGirth_sum_wt_subset
-- name    : ErdosGirth.sum_wt_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:01.044673+00:00
-- url     : https://prove2.me/theorems/29c5bf34-98de-4966-a68b-778aef9079d6
-- title:
--   Erdos Girth: sum wt subset
-- statement:
--   The Erdos Girth construction uses the sum wt subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L40-L57
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L40-L57

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth

theorem ErdosGirth.sum_wt_subset {m : ℕ} (p : ℝ) {A : Finset (Sym2 (Fin m))} (hA : A ⊆ pairs m) :
    ∑ S ∈ (pairs m).powerset, (if A ⊆ S then wt m p S else 0) = p ^ A.card := by sorry
