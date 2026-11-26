-- Prove2me | Theorems.Thm_C6BipartiteDomination_lemma_8_1_add_vertex_criterion
-- name    : C6BipartiteDomination.lemma_8_1_add_vertex_criterion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:50:00.658492+00:00
-- url     : https://prove2.me/theorems/ad314797-5430-41a1-afec-edb207b91105
-- title:
--   C6 Bipartite Domination: lemma 8 1 add vertex criterion
-- statement:
--   Lemma 8.1, in an equivalent coloring formulation: adding `w` preserves
--   bipartiteness exactly when the coloring of `B` can be chosen so every
--   `B`-neighbor of `w` lies on one side. Independent components may be flipped
--   separately to obtain such a coloring.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A8.lean#L67-L85
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A8.lean#L67-L85

import Definitions.Def_C6BipartiteDomination_A7
import Definitions.Def_C6BipartiteDomination_A8
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.lemma_8_1_add_vertex_criterion
    {B : Finset V} {w : V} (hwB : w ∉ B) :
    IsBipartiteOn G (B ∪ {w}) ↔
      ∃ c : V → Bool, ∃ c₀ : Bool,
        (∀ ⦃u v⦄, u ∈ B → v ∈ B → G.Adj u v → c u ≠ c v) ∧
        ∀ v ∈ B, G.Adj w v → c v = c₀ := by sorry
