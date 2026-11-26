-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_negative_debt_paid
-- name    : C6BipartiteDomination.paper11_negative_debt_paid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:01:39.400172+00:00
-- url     : https://prove2.me/theorems/6fe12d1b-9a67-4f4b-8f9d-4e4d94c59531
-- title:
--   C6 Bipartite Domination: paper11 negative debt paid
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 negative debt paid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L899-L956
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L899-L956

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_negative_debt_paid {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (hNoIso : HasNoIsolatedVertices G) :
    (∑ w ∈ paper11NegativeSupports G D, -externalCharge G D w) ≤
      (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
        vertexCharge G D u) +
      (∑ q ∈ paper11AllCompensation G D hCan hmax,
        externalCharge G D q) +
      7 * ((incidenceTotal G D - (Z0Part G D).card : ℕ) : ℤ) := by sorry
