-- Prove2me | Theorems.Thm_C6BipartiteDomination_main_upper_bound_minimum
-- name    : C6BipartiteDomination.main_upper_bound_minimum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:02:28.576297+00:00
-- url     : https://prove2.me/theorems/f526c6ba-02e2-44d1-9b86-dfa1d46dc57c
-- title:
--   C6 Bipartite Domination: main upper bound minimum
-- statement:
--   The C6 Bipartite Domination construction uses the main upper bound minimum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L296-L301
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L296-L301

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.main_upper_bound_minimum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hNoIso : HasNoIsolatedVertices G)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (D : Finset V) (hmin : MinimumBipartiteDominatingSet G D) :
    15 * D.card ≤ 8 * Fintype.card V := by sorry
