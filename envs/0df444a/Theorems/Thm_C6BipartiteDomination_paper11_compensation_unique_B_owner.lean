-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_compensation_unique_B_owner
-- name    : C6BipartiteDomination.paper11_compensation_unique_B_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:56:38.606599+00:00
-- url     : https://prove2.me/theorems/723376c2-3da5-4453-8441-43e03a5b3ffa
-- title:
--   C6 Bipartite Domination: paper11 compensation unique B owner
-- statement:
--   A compensation point has a unique selected `B`-neighbor. This proof
--   uses the exact `D`-restricted neighborhood recorded by `sharedCompensation`.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L478-L498
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L478-L498

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_compensation_unique_B_owner {D X Y : Finset V} {u v q : V}
    (hX : X ⊆ Z0Part G D) (hY : Y ⊆ Z0Part G D)
    (huB : u ∈ BPart G D) (hvB : v ∈ BPart G D)
    (hqU : q ∈ sharedCompensation G D X u)
    (hqV : q ∈ sharedCompensation G D Y v) : u = v := by sorry
