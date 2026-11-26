-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K4Edges_subset_product
-- name    : C6BipartiteDomination.paper11K4Edges_subset_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:37.585478+00:00
-- url     : https://prove2.me/theorems/8ce73111-b1f9-5adc-b2d4-c707a38a939d
-- title:
--   C6 Bipartite Domination: paper11 K4 Edges subset product
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K4 Edges subset product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L61-L80
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L61-L80

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K4Edges_subset_product {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    paper11K4Edges G D hCan hmax ⊆
      (paper11K4Supports G D).product
        (paper11K4RightVertices G D hCan hmax) := by sorry
