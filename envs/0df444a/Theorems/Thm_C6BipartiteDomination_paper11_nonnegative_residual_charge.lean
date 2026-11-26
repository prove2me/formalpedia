-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_nonnegative_residual_charge
-- name    : C6BipartiteDomination.paper11_nonnegative_residual_charge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:01:05.030404+00:00
-- url     : https://prove2.me/theorems/69dde603-e01d-54a8-9dfa-affcd3ab502c
-- title:
--   C6 Bipartite Domination: paper11 nonnegative residual charge
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 nonnegative residual charge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L778-L794
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L778-L794

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_nonnegative_residual_charge {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    0 ≤ ∑ q ∈ paper11NonnegativeSupports G D \
        paper11AllCompensation G D hCan hmax, externalCharge G D q := by sorry
