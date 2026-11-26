-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_negative_debt_split
-- name    : C6BipartiteDomination.paper11_negative_debt_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:00:37.458851+00:00
-- url     : https://prove2.me/theorems/d15988ac-f72f-4ca4-baa9-12db9b00213a
-- title:
--   C6 Bipartite Domination: paper11 negative debt split
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 negative debt split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L663-L670
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L663-L670

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_negative_debt_split {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ w ∈ paper11NegativeSupports G D, -externalCharge G D w) =
      (∑ w ∈ paper11K3Supports G D, -externalCharge G D w) +
      (∑ w ∈ paper11K4Supports G D, -externalCharge G D w) := by sorry
