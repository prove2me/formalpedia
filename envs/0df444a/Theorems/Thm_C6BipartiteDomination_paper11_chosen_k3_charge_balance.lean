-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_chosen_k3_charge_balance
-- name    : C6BipartiteDomination.paper11_chosen_k3_charge_balance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:34.766618+00:00
-- url     : https://prove2.me/theorems/ca270f83-1d3a-5787-ba41-523260b6d10c
-- title:
--   C6 Bipartite Domination: paper11 chosen k3 charge balance
-- statement:
--   Actual degree table adapter for Lemma 11.1 on the fixed chosen relation.
--   The `k=4` part has already been removed by `paper11_k4_separate_support`.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L919-L939
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L919-L939

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_chosen_k3_charge_balance {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ w ∈ paper11K3Supports G D, -externalCharge G D w) ≤
      ∑ u ∈ paper11K3RightVertices G D hCan hmax,
        paper11K3AvailableResource G D hCan hmax u := by sorry
