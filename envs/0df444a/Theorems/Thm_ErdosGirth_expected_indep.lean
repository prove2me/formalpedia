-- Prove2me | Theorems.Thm_ErdosGirth_expected_indep
-- name    : ErdosGirth.expected_indep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:23.400625+00:00
-- url     : https://prove2.me/theorems/7f956bed-44a5-5b28-8ab0-5796e81b1667
-- title:
--   Erdos Girth: expected indep
-- statement:
--   The Erdos Girth construction uses the expected indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L205-L218
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L205-L218

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth

theorem ErdosGirth.expected_indep {m : ℕ} (t : ℕ) (p : ℝ) :
    ∑ S ∈ (pairs m).powerset, wt m p S * indep m t S = m.choose t * (1 - p) ^ t.choose 2 := by sorry
