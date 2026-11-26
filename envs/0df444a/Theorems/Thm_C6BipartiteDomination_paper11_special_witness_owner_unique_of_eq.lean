-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_special_witness_owner_unique_of_eq
-- name    : C6BipartiteDomination.paper11_special_witness_owner_unique_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:21.306893+00:00
-- url     : https://prove2.me/theorems/d8be282d-0cb9-45ce-99ef-850bd26855ba
-- title:
--   C6 Bipartite Domination: paper11 special witness owner unique of eq
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 special witness owner unique of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L758-L765
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L758-L765

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_special_witness_owner_unique_of_eq {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {q₁ q₂ : V}
    (hq : q₁ = q₂)
    (d₁ : Paper10SpecialWitness G hCan hmax q₁)
    (d₂ : Paper10SpecialWitness G hCan hmax q₂) : d₁.u = d₂.u := by sorry
