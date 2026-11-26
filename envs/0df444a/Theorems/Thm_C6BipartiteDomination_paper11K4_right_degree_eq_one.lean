-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K4_right_degree_eq_one
-- name    : C6BipartiteDomination.paper11K4_right_degree_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:58:37.1038+00:00
-- url     : https://prove2.me/theorems/fe0048b6-e635-4826-b635-c5bfb4494f69
-- title:
--   C6 Bipartite Domination: paper11 K4 right degree eq one
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K4 right degree eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L155-L195
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L155-L195

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K4_right_degree_eq_one {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K4RightVertices G D hCan hmax) :
    paper11RightDegree (paper11K4Edges G D hCan hmax)
      (paper11K4Supports G D) u = 1 := by sorry
