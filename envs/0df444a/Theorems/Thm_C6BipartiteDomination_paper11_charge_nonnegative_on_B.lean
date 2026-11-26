-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_charge_nonnegative_on_B
-- name    : C6BipartiteDomination.paper11_charge_nonnegative_on_B
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:00:33.491801+00:00
-- url     : https://prove2.me/theorems/7e34f960-9103-57d2-a16d-4976b10636b1
-- title:
--   C6 Bipartite Domination: paper11 charge nonnegative on B
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 charge nonnegative on B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L675-L685
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L675-L685

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_charge_nonnegative_on_B {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ BPart G D) :
    0 ≤ vertexCharge G D u := by sorry
