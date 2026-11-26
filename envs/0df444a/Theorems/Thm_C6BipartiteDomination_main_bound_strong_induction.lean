-- Prove2me | Theorems.Thm_C6BipartiteDomination_main_bound_strong_induction
-- name    : C6BipartiteDomination.main_bound_strong_induction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:02:22.892419+00:00
-- url     : https://prove2.me/theorems/7943160c-94e6-510c-b99d-d249b7657dd0
-- title:
--   C6 Bipartite Domination: main bound strong induction
-- statement:
--   Strong-induction form of the main bound; the vertex type may change to
--   the subtype used for a proper induced subgraph.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L220-L294
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L220-L294

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.main_bound_strong_induction :
    ∀ n : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V), Fintype.card V = n →
      HasNoIsolatedVertices G →
      (∀ v, degreeTo G Finset.univ v ≤ 6) →
      ∀ D, MinimumBipartiteDominatingSet G D → 15 * D.card ≤ 8 * n := by sorry
