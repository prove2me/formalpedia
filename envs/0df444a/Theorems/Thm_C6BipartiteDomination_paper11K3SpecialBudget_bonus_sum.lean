-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K3SpecialBudget_bonus_sum
-- name    : C6BipartiteDomination.paper11K3SpecialBudget_bonus_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:18.758829+00:00
-- url     : https://prove2.me/theorems/d521ed00-79e2-445d-81f1-6941a97b3fcc
-- title:
--   C6 Bipartite Domination: paper11 K3 Special Budget bonus sum
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K3 Special Budget bonus sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L855-L873
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L855-L873

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K3SpecialBudget_bonus_sum {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11K3RightVertices G D hCan hmax,
      if u ∈ paper11K3SpecialBudgetVertices G D hCan hmax then (7 : ℤ)
      else 0) =
      7 * ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ) := by sorry
