-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K3_edge_mem
-- name    : C6BipartiteDomination.paper11K3_edge_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:56:10.204383+00:00
-- url     : https://prove2.me/theorems/ae8a784d-4f65-4631-85f1-283c1dc652bf
-- title:
--   C6 Bipartite Domination: paper11 K3 edge mem
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K3 edge mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L223-L230
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L223-L230

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K3_edge_mem {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w u : V} :
    (w, u) ∈ paper11K3Edges G D hCan hmax ↔
      w ∈ paper11K3Supports G D ∧
        u ∈ paperChosenRepairSet G D hCan hmax w := by sorry
