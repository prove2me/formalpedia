-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11OwnerCompensation_disjoint
-- name    : C6BipartiteDomination.paper11OwnerCompensation_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:05:12.617875+00:00
-- url     : https://prove2.me/theorems/68f4b770-fdfd-5a02-9d63-5937cf2e6b5e
-- title:
--   C6 Bipartite Domination: paper11 Owner Compensation disjoint
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 Owner Compensation disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L511-L528
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L511-L528

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11OwnerCompensation_disjoint {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u v : V}
    (huB : u ∈ BPart G D) (hvB : v ∈ BPart G D) (hne : u ≠ v) :
    Disjoint (paper11OwnerCompensation G D hCan hmax u)
      (paper11OwnerCompensation G D hCan hmax v) := by sorry
