-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_special_witness_owner_unique
-- name    : C6BipartiteDomination.paper11_special_witness_owner_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:13.534924+00:00
-- url     : https://prove2.me/theorems/b8ed8d5b-4030-4d4d-9126-64b0c8f75329
-- title:
--   C6 Bipartite Domination: paper11 special witness owner unique
-- statement:
--   Any two Section 10 witnesses for the same special compensation point
--   name the same selected `B`-owner.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L745-L756
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L745-L756

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_special_witness_owner_unique {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {q : V}
    (d₁ d₂ : Paper10SpecialWitness G hCan hmax q) : d₁.u = d₂.u := by sorry
