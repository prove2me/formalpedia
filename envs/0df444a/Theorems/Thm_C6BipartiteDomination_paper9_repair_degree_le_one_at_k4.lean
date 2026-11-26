-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper9_repair_degree_le_one_at_k4
-- name    : C6BipartiteDomination.paper9_repair_degree_le_one_at_k4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:55:49.846712+00:00
-- url     : https://prove2.me/theorems/029a698e-38da-47c6-925d-e2546de4dad9
-- title:
--   C6 Bipartite Domination: paper9 repair degree le one at k4
-- statement:
--   The strengthened clause of Lemma 9.1: if the incident family contains a
--   chosen repair edge for a negative vertex with `k=4`, then it has size at most
--   one.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L538-L597
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L538-L597

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper9_repair_degree_le_one_at_k4
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {u w₄ : V} (huB : u ∈ BPart G D) (T : Finset V)
    (hTsub : T ⊆ SPart G D)
    (hTnegative : ∀ w ∈ T, externalCharge G D w < 0)
    (hTrepair : ∀ w ∈ T,
      u ∈ paperChosenRepairSet G D hCan hmax w)
    (hw₄ : w₄ ∈ T) (hk₄ : kCharge G D w₄ = 4) :
    T.card ≤ 1 := by sorry
