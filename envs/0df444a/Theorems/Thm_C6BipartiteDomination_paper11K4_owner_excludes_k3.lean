-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K4_owner_excludes_k3
-- name    : C6BipartiteDomination.paper11K4_owner_excludes_k3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:58:21.875808+00:00
-- url     : https://prove2.me/theorems/bbfe59d3-f820-4574-a5ae-5a32179d5a8f
-- title:
--   C6 Bipartite Domination: paper11 K4 owner excludes k3
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K4 owner excludes k3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L197-L238
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L197-L238

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K4_owner_excludes_k3 {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K4RightVertices G D hCan hmax) :
    u ∉ paper11K3RightVertices G D hCan hmax := by sorry
