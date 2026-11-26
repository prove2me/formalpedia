-- Prove2me | Theorems.Thm_C6BipartiteDomination_beta_ge_two_of_k_ge_two
-- name    : C6BipartiteDomination.beta_ge_two_of_k_ge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:47:22.631362+00:00
-- url     : https://prove2.me/theorems/2ff1669c-9d8b-5fa6-8060-6cd3a6d01cc1
-- title:
--   C6 Bipartite Domination: beta ge two of k ge two
-- statement:
--   The C6 Bipartite Domination construction uses the beta ge two of k ge two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L255-L268
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L255-L268

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.beta_ge_two_of_k_ge_two
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    {w : V} (hw : w ∈ SPart G D)
    (hk : 2 ≤ kCharge G D w) :
    2 ≤ betaCharge G D w := by sorry
