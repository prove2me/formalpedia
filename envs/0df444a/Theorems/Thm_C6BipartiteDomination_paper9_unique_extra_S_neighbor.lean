-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper9_unique_extra_S_neighbor
-- name    : C6BipartiteDomination.paper9_unique_extra_S_neighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:54:52.623165+00:00
-- url     : https://prove2.me/theorems/66fa8100-b0da-569a-b8e9-b905f9127378
-- title:
--   C6 Bipartite Domination: paper9 unique extra S neighbor
-- statement:
--   With two fixed high-support neighbors and at most three `S`-neighbors in
--   total, there is at most one further `S`-neighbor outside the pair.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L414-L441
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L414-L441

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper9_unique_extra_S_neighbor
    {D T : Finset V} {u q r : V}
    (hT : T ⊆ (SPart G D).filter (fun v => G.Adj u v))
    (hTcard : T.card = 2)
    (hq : q ∈ (SPart G D).filter (fun v => G.Adj u v))
    (hr : r ∈ (SPart G D).filter (fun v => G.Adj u v))
    (hqT : q ∉ T) (hrT : r ∉ T)
    (hs : sCharge G D u ≤ 3) : q = r := by sorry
