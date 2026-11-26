-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_incidence_degree_sum
-- name    : C6BipartiteDomination.paper11_incidence_degree_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:56:38.543656+00:00
-- url     : https://prove2.me/theorems/6d756691-5d55-480c-a25d-d254382f4e7c
-- title:
--   C6 Bipartite Domination: paper11 incidence degree sum
-- statement:
--   The finite incidence-count identity needed for charge balance.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L26-L50
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L26-L50

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem C6BipartiteDomination.paper11_incidence_degree_sum
    (L R : Finset V) (E : Finset (V × V))
    (hE : E ⊆ L.product R) :
    (∑ w ∈ L, paper11LeftDegree E R w) = E.card ∧
      (∑ u ∈ R, paper11RightDegree E L u) = E.card := by sorry
