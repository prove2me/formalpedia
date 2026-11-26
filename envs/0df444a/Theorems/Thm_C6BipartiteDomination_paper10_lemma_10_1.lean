-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper10_lemma_10_1
-- name    : C6BipartiteDomination.paper10_lemma_10_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:56:42.044011+00:00
-- url     : https://prove2.me/theorems/2e957af3-8c65-495a-8353-297268130bc4
-- title:
--   C6 Bipartite Domination: paper10 lemma 10 1
-- statement:
--   Lemma 10.1: the special vertices inject into the repeated-incidence
--   budget `m - |Z₀|`.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection10.lean#L218-L302
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection10.lean#L218-L302

import Definitions.Def_C6BipartiteDomination_PaperSection9
import Definitions.Def_C6BipartiteDomination_PaperSection10
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper10_lemma_10_1
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (hNoIso : HasNoIsolatedVertices G) :
    (paper10SpecialQSet G hCan hmax).card ≤
      incidenceTotal G D - (Z0Part G D).card := by sorry
