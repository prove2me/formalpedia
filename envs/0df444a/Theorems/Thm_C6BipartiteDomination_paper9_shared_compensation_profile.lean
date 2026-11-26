-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper9_shared_compensation_profile
-- name    : C6BipartiteDomination.paper9_shared_compensation_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:54:04.099223+00:00
-- url     : https://prove2.me/theorems/cd3ad17b-f3e5-4a5f-bb81-12f86d8e799a
-- title:
--   C6 Bipartite Domination: paper9 shared compensation profile
-- statement:
--   A shared compensation vertex is an `S`-neighbor of its repair vertex and
--   has exactly one `Z₀`-neighbor. This is the local incidence fact used in the
--   paper's repair-graph degree argument.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L181-L250
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L181-L250

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper9_shared_compensation_profile
    {D X : Finset V} {u q : V}
    (hX : X ⊆ Z0Part G D) (huB : u ∈ BPart G D)
    (hq : q ∈ sharedCompensation G D X u) :
    q ∈ SPart G D ∧ G.Adj u q ∧ kCharge G D q = 1 := by sorry
