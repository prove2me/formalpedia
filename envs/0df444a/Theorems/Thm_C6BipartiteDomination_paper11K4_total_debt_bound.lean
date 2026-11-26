-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K4_total_debt_bound
-- name    : C6BipartiteDomination.paper11K4_total_debt_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:51.071018+00:00
-- url     : https://prove2.me/theorems/b1df9721-bdee-4a24-8310-bead25292252
-- title:
--   C6 Bipartite Domination: paper11 K4 total debt bound
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K4 total debt bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L294-L362
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L294-L362

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K4_total_debt_bound {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ w ∈ paper11K4Supports G D, -externalCharge G D w) ≤
      ∑ u ∈ paper11K4RightVertices G D hCan hmax,
        paper11K4Resource G D hCan hmax u := by sorry
