-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper9_union_resource_bound
-- name    : C6BipartiteDomination.paper9_union_resource_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:53:54.032291+00:00
-- url     : https://prove2.me/theorems/eff4ff61-d719-5d24-85e1-8f7165ed3b92
-- title:
--   C6 Bipartite Domination: paper9 union resource bound
-- statement:
--   Count a high-support neighbor set and a shared compensation set together
--   inside the `S`-neighbors of `u`.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L397-L410
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L397-L410

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper9_union_resource_bound
    {D T L : Finset V} {u : V}
    (hT : T ⊆ (SPart G D).filter (fun q => G.Adj u q))
    (hL : L ⊆ (SPart G D).filter (fun q => G.Adj u q))
    (hdisj : Disjoint T L) :
    T.card + L.card ≤ sCharge G D u := by sorry
