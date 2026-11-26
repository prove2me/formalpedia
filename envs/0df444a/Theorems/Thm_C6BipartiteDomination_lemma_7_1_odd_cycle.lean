-- Prove2me | Theorems.Thm_C6BipartiteDomination_lemma_7_1_odd_cycle
-- name    : C6BipartiteDomination.lemma_7_1_odd_cycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:47:22.139376+00:00
-- url     : https://prove2.me/theorems/60b6875b-4273-4a30-a52b-10452fa359ac
-- title:
--   C6 Bipartite Domination: lemma 7 1 odd cycle
-- statement:
--   Lemma 7.1: two or more `Z₀`-neighbors of a vertex in `S` would permit a
--   strictly smaller bipartite dominating set.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L194-L253
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L194-L253

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.lemma_7_1_odd_cycle
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    {w : V} (hw : w ∈ SPart G D)
    (hk : 2 ≤ kCharge G D w) :
    ¬ IsBipartiteOn G (BPart G D ∪ {w}) := by sorry
