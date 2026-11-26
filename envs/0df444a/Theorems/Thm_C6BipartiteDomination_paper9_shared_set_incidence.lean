-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper9_shared_set_incidence
-- name    : C6BipartiteDomination.paper9_shared_set_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:53:52.513861+00:00
-- url     : https://prove2.me/theorems/fd5a5dc5-5bd9-539f-91b8-8e3308dd7a2c
-- title:
--   C6 Bipartite Domination: paper9 shared set incidence
-- statement:
--   The shared compensation set lies among the `S`-neighbors of `u`, and is
--   disjoint from any set of support-at-least-two vertices.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L254-L268
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L254-L268

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper9_shared_set_incidence
    {D X : Finset V} {u : V}
    (hX : X ⊆ Z0Part G D) (huB : u ∈ BPart G D) :
    sharedCompensation G D X u ⊆ (SPart G D).filter (fun q => G.Adj u q) ∧
      ∀ T : Finset V, (∀ w ∈ T, 2 ≤ kCharge G D w) →
        Disjoint T (sharedCompensation G D X u) := by sorry
