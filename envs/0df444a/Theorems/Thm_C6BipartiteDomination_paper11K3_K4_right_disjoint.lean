-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K3_K4_right_disjoint
-- name    : C6BipartiteDomination.paper11K3_K4_right_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:45.439906+00:00
-- url     : https://prove2.me/theorems/437efd29-e44b-5347-ae2e-afd6eb7e450c
-- title:
--   C6 Bipartite Domination: paper11 K3 K4 right disjoint
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K3 K4 right disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L240-L247
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L240-L247

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K3_K4_right_disjoint {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    Disjoint (paper11K3RightVertices G D hCan hmax)
      (paper11K4RightVertices G D hCan hmax) := by sorry
