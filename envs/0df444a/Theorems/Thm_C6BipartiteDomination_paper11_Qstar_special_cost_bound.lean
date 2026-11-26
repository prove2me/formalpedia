-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_Qstar_special_cost_bound
-- name    : C6BipartiteDomination.paper11_Qstar_special_cost_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:19.241128+00:00
-- url     : https://prove2.me/theorems/7785ee10-0931-4974-a07c-c9c21bf23c5c
-- title:
--   C6 Bipartite Domination: paper11 Qstar special cost bound
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 Qstar special cost bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L823-L833
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L823-L833

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_Qstar_special_cost_bound {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (hNoIso : HasNoIsolatedVertices G) :
    7 * ((paper10SpecialQSet G hCan hmax).card : ℤ) ≤
      7 * ((incidenceTotal G D - (Z0Part G D).card : ℕ) : ℤ) := by sorry
