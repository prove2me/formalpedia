-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K4_edge_mem
-- name    : C6BipartiteDomination.paper11K4_edge_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:57:58.664105+00:00
-- url     : https://prove2.me/theorems/37befc73-8f81-471c-aec6-7c68595f0fde
-- title:
--   C6 Bipartite Domination: paper11 K4 edge mem
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K4 edge mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L52-L59
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L52-L59

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K4_edge_mem {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w u : V} :
    (w, u) ∈ paper11K4Edges G D hCan hmax ↔
      w ∈ paper11K4Supports G D ∧
        u ∈ paperChosenRepairSet G D hCan hmax w := by sorry
