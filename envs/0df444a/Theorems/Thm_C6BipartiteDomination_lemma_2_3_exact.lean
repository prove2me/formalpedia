-- Prove2me | Theorems.Thm_C6BipartiteDomination_lemma_2_3_exact
-- name    : C6BipartiteDomination.lemma_2_3_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:40:32.850218+00:00
-- url     : https://prove2.me/theorems/52fa939d-74f9-5544-8962-7b55d25a5e3f
-- title:
--   C6 Bipartite Domination: lemma 2 3 exact
-- statement:
--   The exact equality in Lemma 2.3, expressed as a local witness together
--   with minimality against every local bipartite dominating set.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A2.lean#L144-L152
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A2.lean#L144-L152

import Definitions.Def_C6BipartiteDomination_Basic
import Definitions.Def_C6BipartiteDomination_A2
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.lemma_2_3_exact
    {D X : Finset V}
    (hD : MinimumBipartiteDominatingSet G D)
    (hX : IsolatedSubset G D X) :
    BipartiteDominatingOn G (responsibilityRegion G D X) X ∧
      ∀ Y, BipartiteDominatingOn G (responsibilityRegion G D X) Y → X.card ≤ Y.card := by sorry
