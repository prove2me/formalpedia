-- Prove2me | Theorems.Thm_C6BipartiteDomination_isolatedSubset_region_subset
-- name    : C6BipartiteDomination.isolatedSubset_region_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:40:26.296115+00:00
-- url     : https://prove2.me/theorems/3208569a-ae6b-4667-8d98-c71de8875fc7
-- title:
--   C6 Bipartite Domination: isolated Subset region subset
-- statement:
--   The C6 Bipartite Domination construction uses the isolated Subset region subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A2.lean#L50-L60
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A2.lean#L50-L60

import Definitions.Def_C6BipartiteDomination_Basic
import Definitions.Def_C6BipartiteDomination_A2
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.isolatedSubset_region_subset
    {D X : Finset V} (hX : IsolatedSubset G D X) :
    X ⊆ responsibilityRegion G D X := by sorry
