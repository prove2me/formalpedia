-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K3SpecialBudget_card_le_Qstar
-- name    : C6BipartiteDomination.paper11K3SpecialBudget_card_le_Qstar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:17.967068+00:00
-- url     : https://prove2.me/theorems/dacfb7b7-a074-5594-be53-a79eda050c13
-- title:
--   C6 Bipartite Domination: paper11 K3 Special Budget card le Qstar
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K3 Special Budget card le Qstar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L793-L821
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L793-L821

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K3SpecialBudget_card_le_Qstar {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (paper11K3SpecialBudgetVertices G D hCan hmax).card ≤
      (paper10SpecialQSet G hCan hmax).card := by sorry
