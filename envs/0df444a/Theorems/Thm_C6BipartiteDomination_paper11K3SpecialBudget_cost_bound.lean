-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K3SpecialBudget_cost_bound
-- name    : C6BipartiteDomination.paper11K3SpecialBudget_cost_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:57:13.6544+00:00
-- url     : https://prove2.me/theorems/16cdec1a-8540-5fa5-8502-1314ef5fc5e0
-- title:
--   C6 Bipartite Domination: paper11 K3 Special Budget cost bound
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K3 Special Budget cost bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L835-L845
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L835-L845

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K3SpecialBudget_cost_bound {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (hNoIso : HasNoIsolatedVertices G) :
    7 * ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ) ≤
      7 * ((incidenceTotal G D - (Z0Part G D).card : ℕ) : ℤ) := by sorry
