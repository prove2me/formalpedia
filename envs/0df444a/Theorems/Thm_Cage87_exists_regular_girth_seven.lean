-- Prove2me | Theorems.Thm_Cage87_exists_regular_girth_seven
-- name    : Cage87.exists_regular_girth_seven
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:27:46.550999+00:00
-- url     : https://prove2.me/theorems/a11ce73d-6356-471f-bd73-39b227fa6ccb
-- title:
--   Cage87: exists regular girth seven
-- statement:
--   The Cage87 construction uses the exists regular girth seven property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Solution.lean#L18-L20
-- source:
--   https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Solution.lean#L18-L20

module
public import Definitions.Def_Cage87
public import Definitions.Def_Cage87Solution
set_option autoImplicit true
@[expose] public section
public section
open Cage87

theorem Cage87.exists_regular_girth_seven :
    ∃ (G : SimpleGraph (Fin 768)) (_ : DecidableRel G.Adj), G.IsRegularOfDegree 8 ∧ G.girth = 7 := by sorry
