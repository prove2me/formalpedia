-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper9_shared_external_charge_eq_four
-- name    : C6BipartiteDomination.paper9_shared_external_charge_eq_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:54:02.611799+00:00
-- url     : https://prove2.me/theorems/2f6ed068-64e2-498c-884c-494759bb9f1e
-- title:
--   C6 Bipartite Domination: paper9 shared external charge eq four
-- statement:
--   Every shared compensation vertex contributes the paper's positive charge
--   `a(q)=4`.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L316-L325
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L316-L325

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper9_shared_external_charge_eq_four
    {D X : Finset V} {u q : V}
    (hX : X ⊆ Z0Part G D) (huB : u ∈ BPart G D)
    (hq : q ∈ sharedCompensation G D X u) :
    externalCharge G D q = 4 := by sorry
