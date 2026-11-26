-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper10SpecialEndpoint_mem
-- name    : C6BipartiteDomination.paper10SpecialEndpoint_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:56:08.277663+00:00
-- url     : https://prove2.me/theorems/5ac69213-e301-5caa-a609-6fa87ff8a4c5
-- title:
--   C6 Bipartite Domination: paper10 Special Endpoint mem
-- statement:
--   The C6 Bipartite Domination construction uses the paper10 Special Endpoint mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection10.lean#L72-L81
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection10.lean#L72-L81

import Definitions.Def_C6BipartiteDomination_PaperSection9
import Definitions.Def_C6BipartiteDomination_PaperSection10
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper10SpecialEndpoint_mem
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {q : V}
    (hq : IsPaper10SpecialQ G hCan hmax q) :
    ∃ z ∈ Z0Part G D, paper10SpecialEndpoint G hCan hmax q = some z := by sorry
