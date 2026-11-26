-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper9_repair_degree_le_two
-- name    : C6BipartiteDomination.paper9_repair_degree_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:55:22.222909+00:00
-- url     : https://prove2.me/theorems/1ba1614b-be68-4bd2-841a-0f5f4bd265c8
-- title:
--   C6 Bipartite Domination: paper9 repair degree le two
-- statement:
--   Paper Lemma 9.1, right degree at most two, stated for any finite family
--   of chosen repair edges incident with the same `B`-vertex.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L475-L533
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L475-L533

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper9_repair_degree_le_two
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {u : V} (huB : u ∈ BPart G D) (T : Finset V)
    (hTsub : T ⊆ SPart G D)
    (hTnegative : ∀ w ∈ T, externalCharge G D w < 0)
    (hTrepair : ∀ w ∈ T,
      u ∈ paperChosenRepairSet G D hCan hmax w) :
    T.card ≤ 2 := by sorry
