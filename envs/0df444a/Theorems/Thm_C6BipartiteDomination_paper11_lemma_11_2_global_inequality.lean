-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_lemma_11_2_global_inequality
-- name    : C6BipartiteDomination.paper11_lemma_11_2_global_inequality
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:01:35.645067+00:00
-- url     : https://prove2.me/theorems/aad1173c-dd97-57a9-a864-5d993da65202
-- title:
--   C6 Bipartite Domination: paper11 lemma 11 2 global inequality
-- statement:
--   Lemma 11.2: all positive vertex charges, chosen compensation charges,
--   and the Section 10 incidence surplus cover every negative external charge.
--   Combining this with the exact Section 6 identity gives the asserted global
--   inequality.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L986-L1053
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L986-L1053

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_lemma_11_2_global_inequality {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (hNoIso : HasNoIsolatedVertices G) :
    8 * (WBPart G D).card ≥
      7 * ((BPart G D).card + (Z0Part G D).card) := by sorry
