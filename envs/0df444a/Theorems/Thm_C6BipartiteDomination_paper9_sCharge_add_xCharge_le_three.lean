-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper9_sCharge_add_xCharge_le_three
-- name    : C6BipartiteDomination.paper9_sCharge_add_xCharge_le_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:53:49.990049+00:00
-- url     : https://prove2.me/theorems/6831b7f7-189e-5441-99aa-0a8f72a0adf8
-- title:
--   C6 Bipartite Domination: paper9 s Charge add x Charge le three
-- statement:
--   The local degree budget used at the start of Lemma 9.1.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L155-L176
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L155-L176

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper9_sCharge_add_xCharge_le_three
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {u : V} (huB : u ∈ BPart G D) :
    sCharge G D u + xCharge G D u ≤ 3 := by sorry
