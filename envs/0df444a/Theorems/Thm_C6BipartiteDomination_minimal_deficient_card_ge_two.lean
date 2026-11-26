-- Prove2me | Theorems.Thm_C6BipartiteDomination_minimal_deficient_card_ge_two
-- name    : C6BipartiteDomination.minimal_deficient_card_ge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:41:29.300729+00:00
-- url     : https://prove2.me/theorems/ccacfe2c-72f1-5595-aad0-2df19cee6e07
-- title:
--   C6 Bipartite Domination: minimal deficient card ge two
-- statement:
--   The C6 Bipartite Domination construction uses the minimal deficient card ge two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L113-L136
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L113-L136

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.minimal_deficient_card_ge_two
    {D X : Finset V} (hXsub : X ⊆ D)
    (hDind : Independent G D) (hNoIso : HasNoIsolatedVertices G)
    (hdef : (neighborsIn G X (Finset.univ \ D)).card < X.card) :
    2 ≤ X.card := by sorry
